import V185TrunkScan23Chunk0479

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2839099 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 4]
def baseStart_2839099 : Nat := 118140960795 + 2839099 * 2 ^ 59
def prefixEnd_2839099 : Nat := 4983230072969 + 3 ^ 40 * 2839099 * 2
def baseEnd_2839099 : Nat := 1457822412699292745805727

theorem tailTrace_2839099 : CollatzResearch.WordTrace tailWord_2839099 prefixEnd_2839099 1457822412699292745805727 := by
  unfold tailWord_2839099
  simp only [CollatzResearch.WordTrace]
  refine ⟨103550447541436677351080351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69033631694291118234053567 103550447541436677351080351)
  ·
    refine ⟨155325671312155016026620527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103550447541436677351080351 155325671312155016026620527)
    ·
      refine ⟨232988506968232524039930791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155325671312155016026620527 232988506968232524039930791)
      ·
        refine ⟨349482760452348786059896187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232988506968232524039930791 349482760452348786059896187)
        ·
          refine ⟨524224140678523179089844281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349482760452348786059896187 524224140678523179089844281)
          ·
            refine ⟨393168105508892384317383211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524224140678523179089844281 393168105508892384317383211)
            ·
              refine ⟨589752158263338576476074817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393168105508892384317383211 589752158263338576476074817)
              ·
                refine ⟨442314118697503932357056113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589752158263338576476074817 442314118697503932357056113)
                ·
                  refine ⟨331735589023127949267792085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442314118697503932357056113 331735589023127949267792085)
                  ·
                    refine ⟨7775052867729561310963877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 331735589023127949267792085 7775052867729561310963877)
                    ·
                      refine ⟨1457822412699292745805727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7775052867729561310963877 1457822412699292745805727)
                      ·
                        rfl

theorem cell23_2839099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 4].length) (baseStart_2839099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839099 prefixEnd_2839099 := by exact prefixLift 2839099
  have htrace : WordTrace (prefixWord ++ tailWord_2839099) baseStart_2839099 baseEnd_2839099 := by
    simpa [prefixWord, tailWord_2839099, baseEnd_2839099] using wordTrace_append hprefix tailTrace_2839099
  have hstable : (prefixWord ++ tailWord_2839099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839099).length < 2 ^ (prefixWord ++ tailWord_2839099).sum := by decide
  have hdescent : baseEnd_2839099 < baseStart_2839099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839116 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_2839116 : Nat := 118140960795 + 2839116 * 2 ^ 59
def prefixEnd_2839116 : Nat := 4983230072969 + 3 ^ 40 * 2839116 * 2
def baseEnd_2839116 : Nat := 1457831141870419179293149

theorem tailTrace_2839116 : CollatzResearch.WordTrace tailWord_2839116 prefixEnd_2839116 1457831141870419179293149 := by
  unfold tailWord_2839116
  simp only [CollatzResearch.WordTrace]
  refine ⟨51775533791187544627224601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69034045054916726169632801 51775533791187544627224601)
  ·
    refine ⟨38831650343390658470418451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51775533791187544627224601 38831650343390658470418451)
    ·
      refine ⟨58247475515085987705627677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38831650343390658470418451 58247475515085987705627677)
      ·
        refine ⟨21842803318157245389610379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58247475515085987705627677 21842803318157245389610379)
        ·
          refine ⟨32764204977235868084415569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21842803318157245389610379 32764204977235868084415569)
          ·
            refine ⟨24573153732926901063311677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32764204977235868084415569 24573153732926901063311677)
            ·
              refine ⟨9214932649847587898741879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24573153732926901063311677 9214932649847587898741879)
              ·
                refine ⟨13822398974771381848112819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9214932649847587898741879 13822398974771381848112819)
                ·
                  refine ⟨20733598462157072772169229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13822398974771381848112819 20733598462157072772169229)
                  ·
                    refine ⟨7775099423308902289563461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20733598462157072772169229 7775099423308902289563461)
                    ·
                      refine ⟨1457831141870419179293149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7775099423308902289563461 1457831141870419179293149)
                      ·
                        rfl

theorem cell23_2839116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_2839116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839116 prefixEnd_2839116 := by exact prefixLift 2839116
  have htrace : WordTrace (prefixWord ++ tailWord_2839116) baseStart_2839116 baseEnd_2839116 := by
    simpa [prefixWord, tailWord_2839116, baseEnd_2839116] using wordTrace_append hprefix tailTrace_2839116
  have hstable : (prefixWord ++ tailWord_2839116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839116).length < 2 ^ (prefixWord ++ tailWord_2839116).sum := by decide
  have hdescent : baseEnd_2839116 < baseStart_2839116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839146 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2839146 : Nat := 118140960795 + 2839146 * 2 ^ 59
def prefixEnd_2839146 : Nat := 4983230072969 + 3 ^ 40 * 2839146 * 2
def baseEnd_2839146 : Nat := 1457846546290054061918011

theorem tailTrace_2839146 : CollatzResearch.WordTrace tailWord_2839146 prefixEnd_2839146 1457846546290054061918011 := by
  unfold tailWord_2839146
  simp only [CollatzResearch.WordTrace]
  refine ⟨25888040443066601094510323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69034774514844269585360861 25888040443066601094510323)
  ·
    refine ⟨38832060664599901641765485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25888040443066601094510323 38832060664599901641765485)
    ·
      refine ⟨14562022749224963115662057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38832060664599901641765485 14562022749224963115662057)
      ·
        refine ⟨10921517061918722336746543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14562022749224963115662057 10921517061918722336746543)
        ·
          refine ⟨16382275592878083505119815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10921517061918722336746543 16382275592878083505119815)
          ·
            refine ⟨24573413389317125257679723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16382275592878083505119815 24573413389317125257679723)
            ·
              refine ⟨36860120083975687886519585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24573413389317125257679723 36860120083975687886519585)
              ·
                refine ⟨27645090062981765914889689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36860120083975687886519585 27645090062981765914889689)
                ·
                  refine ⟨20733817547236324436167267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27645090062981765914889689 20733817547236324436167267)
                  ·
                    refine ⟨31100726320854486654250901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20733817547236324436167267 31100726320854486654250901)
                    ·
                      refine ⟨1457846546290054061918011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31100726320854486654250901 1457846546290054061918011)
                      ·
                        rfl

theorem cell23_2839146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2839146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839146 prefixEnd_2839146 := by exact prefixLift 2839146
  have htrace : WordTrace (prefixWord ++ tailWord_2839146) baseStart_2839146 baseEnd_2839146 := by
    simpa [prefixWord, tailWord_2839146, baseEnd_2839146] using wordTrace_append hprefix tailTrace_2839146
  have hstable : (prefixWord ++ tailWord_2839146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839146).length < 2 ^ (prefixWord ++ tailWord_2839146).sum := by decide
  have hdescent : baseEnd_2839146 < baseStart_2839146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839150 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_2839150 : Nat := 118140960795 + 2839150 * 2 ^ 59
def prefixEnd_2839150 : Nat := 4983230072969 + 3 ^ 40 * 2839150 * 2
def baseEnd_2839150 : Nat := 1457848600212672046267993

theorem tailTrace_2839150 : CollatzResearch.WordTrace tailWord_2839150 prefixEnd_2839150 1457848600212672046267993 := by
  unfold tailWord_2839150
  simp only [CollatzResearch.WordTrace]
  refine ⟨12944038458031489132648363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69034871776167942040791269 12944038458031489132648363)
  ·
    refine ⟨19416057687047233698972545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12944038458031489132648363 19416057687047233698972545)
    ·
      refine ⟨14562043265285425274229409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19416057687047233698972545 14562043265285425274229409)
      ·
        refine ⟨10921532448964068955672057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14562043265285425274229409 10921532448964068955672057)
        ·
          refine ⟨8191149336723051716754043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10921532448964068955672057 8191149336723051716754043)
          ·
            refine ⟨12286724005084577575131065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8191149336723051716754043 12286724005084577575131065)
            ·
              refine ⟨9215043003813433181348299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12286724005084577575131065 9215043003813433181348299)
              ·
                refine ⟨13822564505720149772022449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9215043003813433181348299 13822564505720149772022449)
                ·
                  refine ⟨10366923379290112329016837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13822564505720149772022449 10366923379290112329016837)
                  ·
                    refine ⟨1943798133616896061690657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10366923379290112329016837 1943798133616896061690657)
                    ·
                      refine ⟨1457848600212672046267993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1943798133616896061690657 1457848600212672046267993)
                      ·
                        rfl

theorem cell23_2839150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_2839150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839150 prefixEnd_2839150 := by exact prefixLift 2839150
  have htrace : WordTrace (prefixWord ++ tailWord_2839150) baseStart_2839150 baseEnd_2839150 := by
    simpa [prefixWord, tailWord_2839150, baseEnd_2839150] using wordTrace_append hprefix tailTrace_2839150
  have hstable : (prefixWord ++ tailWord_2839150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839150).length < 2 ^ (prefixWord ++ tailWord_2839150).sum := by decide
  have hdescent : baseEnd_2839150 < baseStart_2839150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839194 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 3, 4]
def baseStart_2839194 : Nat := 118140960795 + 2839194 * 2 ^ 59
def prefixEnd_2839194 : Nat := 4983230072969 + 3 ^ 40 * 2839194 * 2
def baseEnd_2839194 : Nat := 485957064453823291372597

theorem tailTrace_2839194 : CollatzResearch.WordTrace tailWord_2839194 prefixEnd_2839194 485957064453823291372597 := by
  unfold tailWord_2839194
  simp only [CollatzResearch.WordTrace]
  refine ⟨25888478119023127143947159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69035941650728339050525757 25888478119023127143947159)
  ·
    refine ⟨38832717178534690715920739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25888478119023127143947159 38832717178534690715920739)
    ·
      refine ⟨58249075767802036073881109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38832717178534690715920739 58249075767802036073881109)
      ·
        refine ⟨2730425426615720440963177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58249075767802036073881109 2730425426615720440963177)
        ·
          refine ⟨2047819069961790330722383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2730425426615720440963177 2047819069961790330722383)
          ·
            refine ⟨3071728604942685496083575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047819069961790330722383 3071728604942685496083575)
            ·
              refine ⟨4607592907414028244125363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3071728604942685496083575 4607592907414028244125363)
              ·
                refine ⟨6911389361121042366188045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4607592907414028244125363 6911389361121042366188045)
                ·
                  refine ⟨2591771010420390887320517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6911389361121042366188045 2591771010420390887320517)
                  ·
                    refine ⟨485957064453823291372597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2591771010420390887320517 485957064453823291372597)
                    ·
                      rfl

theorem cell23_2839194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_2839194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839194 prefixEnd_2839194 := by exact prefixLift 2839194
  have htrace : WordTrace (prefixWord ++ tailWord_2839194) baseStart_2839194 baseEnd_2839194 := by
    simpa [prefixWord, tailWord_2839194, baseEnd_2839194] using wordTrace_append hprefix tailTrace_2839194
  have hstable : (prefixWord ++ tailWord_2839194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839194).length < 2 ^ (prefixWord ++ tailWord_2839194).sum := by decide
  have hdescent : baseEnd_2839194 < baseStart_2839194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839216 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 1, 6]
def baseStart_2839216 : Nat := 118140960795 + 2839216 * 2 ^ 59
def prefixEnd_2839216 : Nat := 4983230072969 + 3 ^ 40 * 2839216 * 2
def baseEnd_2839216 : Nat := 485960829978622929347563

theorem tailTrace_2839216 : CollatzResearch.WordTrace tailWord_2839216 prefixEnd_2839216 485960829978622929347563 := by
  unfold tailWord_2839216
  simp only [CollatzResearch.WordTrace]
  refine ⟨51777357441006403166544751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69036476588008537555393001 51777357441006403166544751)
  ·
    refine ⟨77666036161509604749817127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51777357441006403166544751 77666036161509604749817127)
    ·
      refine ⟨116499054242264407124725691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77666036161509604749817127 116499054242264407124725691)
      ·
        refine ⟨174748581363396610687088537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116499054242264407124725691 174748581363396610687088537)
        ·
          refine ⟨131061436022547458015316403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174748581363396610687088537 131061436022547458015316403)
          ·
            refine ⟨196592154033821187022974605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131061436022547458015316403 196592154033821187022974605)
            ·
              refine ⟨73722057762682945133615477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196592154033821187022974605 73722057762682945133615477)
              ·
                refine ⟨6911442915251526106276451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73722057762682945133615477 6911442915251526106276451)
                ·
                  refine ⟨10367164372877289159414677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6911442915251526106276451 10367164372877289159414677)
                  ·
                    refine ⟨485960829978622929347563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10367164372877289159414677 485960829978622929347563)
                    ·
                      rfl

theorem cell23_2839216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 6].length) (baseStart_2839216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839216 prefixEnd_2839216 := by exact prefixLift 2839216
  have htrace : WordTrace (prefixWord ++ tailWord_2839216) baseStart_2839216 baseEnd_2839216 := by
    simpa [prefixWord, tailWord_2839216, baseEnd_2839216] using wordTrace_append hprefix tailTrace_2839216
  have hstable : (prefixWord ++ tailWord_2839216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839216).length < 2 ^ (prefixWord ++ tailWord_2839216).sum := by decide
  have hdescent : baseEnd_2839216 < baseStart_2839216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839246 : List Nat := [4, 1, 1, 1, 3, 13]
def baseStart_2839246 : Nat := 118140960795 + 2839246 * 2 ^ 59
def prefixEnd_2839246 : Nat := 4983230072969 + 3 ^ 40 * 2839246 * 2
def baseEnd_2839246 : Nat := 5999579812162566545957

theorem tailTrace_2839246 : CollatzResearch.WordTrace tailWord_2839246 prefixEnd_2839246 5999579812162566545957 := by
  unfold tailWord_2839246
  simp only [CollatzResearch.WordTrace]
  refine ⟨12944476133988015182085199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69037206047936080971121061 12944476133988015182085199)
  ·
    refine ⟨19416714200982022773127799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12944476133988015182085199 19416714200982022773127799)
    ·
      refine ⟨29125071301473034159691699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19416714200982022773127799 29125071301473034159691699)
      ·
        refine ⟨43687606952209551239537549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29125071301473034159691699 43687606952209551239537549)
        ·
          refine ⟨16382852607078581714826581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43687606952209551239537549 16382852607078581714826581)
          ·
            refine ⟨5999579812162566545957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 16382852607078581714826581 5999579812162566545957)
            ·
              rfl

theorem cell23_2839246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 13].length) (baseStart_2839246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839246 prefixEnd_2839246 := by exact prefixLift 2839246
  have htrace : WordTrace (prefixWord ++ tailWord_2839246) baseStart_2839246 baseEnd_2839246 := by
    simpa [prefixWord, tailWord_2839246, baseEnd_2839246] using wordTrace_append hprefix tailTrace_2839246
  have hstable : (prefixWord ++ tailWord_2839246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839246).length < 2 ^ (prefixWord ++ tailWord_2839246).sum := by decide
  have hdescent : baseEnd_2839246 < baseStart_2839246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839263 : List Nat := [1, 1, 2, 3, 2, 5, 1, 8]
def baseStart_2839263 : Nat := 118140960795 + 2839263 * 2 ^ 59
def prefixEnd_2839263 : Nat := 4983230072969 + 3 ^ 40 * 2839263 * 2
def baseEnd_2839263 : Nat := 53996541612097411264999

theorem tailTrace_2839263 : CollatzResearch.WordTrace tailWord_2839263 prefixEnd_2839263 53996541612097411264999 := by
  unfold tailWord_2839263
  simp only [CollatzResearch.WordTrace]
  refine ⟨103556429112842533360050443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69037619408561688906700295 103556429112842533360050443)
  ·
    refine ⟨155334643669263800040075665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103556429112842533360050443 155334643669263800040075665)
    ·
      refine ⟨116500982751947850030056749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155334643669263800040075665 116500982751947850030056749)
      ·
        refine ⟨43687868531980443761271281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116500982751947850030056749 43687868531980443761271281)
        ·
          refine ⟨32765901398985332820953461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43687868531980443761271281 32765901398985332820953461)
          ·
            refine ⟨3071803256154874951964387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32765901398985332820953461 3071803256154874951964387)
            ·
              refine ⟨4607704884232312427946581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3071803256154874951964387 4607704884232312427946581)
              ·
                refine ⟨53996541612097411264999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4607704884232312427946581 53996541612097411264999)
                ·
                  rfl

theorem cell23_2839263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 8].length) (baseStart_2839263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839263 prefixEnd_2839263 := by exact prefixLift 2839263
  have htrace : WordTrace (prefixWord ++ tailWord_2839263) baseStart_2839263 baseEnd_2839263 := by
    simpa [prefixWord, tailWord_2839263, baseEnd_2839263] using wordTrace_append hprefix tailTrace_2839263
  have hstable : (prefixWord ++ tailWord_2839263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839263).length < 2 ^ (prefixWord ++ tailWord_2839263).sum := by decide
  have hdescent : baseEnd_2839263 < baseStart_2839263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839273 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 1, 3, 3]
def baseStart_2839273 : Nat := 118140960795 + 2839273 * 2 ^ 59
def prefixEnd_2839273 : Nat := 4983230072969 + 3 ^ 40 * 2839273 * 2
def baseEnd_2839273 : Nat := 1457911758333175065029927

theorem tailTrace_2839273 : CollatzResearch.WordTrace tailWord_2839273 prefixEnd_2839273 1457911758333175065029927 := by
  unfold tailWord_2839273
  simp only [CollatzResearch.WordTrace]
  refine ⟨103556793842806305067914473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69037862561870870045276315 103556793842806305067914473)
  ·
    refine ⟨77667595382104728800935855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103556793842806305067914473 77667595382104728800935855)
    ·
      refine ⟨116501393073157093201403783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77667595382104728800935855 116501393073157093201403783)
      ·
        refine ⟨174752089609735639802105675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116501393073157093201403783 174752089609735639802105675)
        ·
          refine ⟨262128134414603459703158513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174752089609735639802105675 262128134414603459703158513)
          ·
            refine ⟨196596100810952594777368885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262128134414603459703158513 196596100810952594777368885)
            ·
              refine ⟨18430884451026805760378333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 196596100810952594777368885 18430884451026805760378333)
              ·
                refine ⟨6911581669135052160141875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18430884451026805760378333 6911581669135052160141875)
                ·
                  refine ⟨10367372503702578240212813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6911581669135052160141875 10367372503702578240212813)
                  ·
                    refine ⟨3887764688888466840079805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10367372503702578240212813 3887764688888466840079805)
                    ·
                      refine ⟨1457911758333175065029927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3887764688888466840079805 1457911758333175065029927)
                      ·
                        rfl

theorem cell23_2839273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 3, 3].length) (baseStart_2839273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839273 prefixEnd_2839273 := by exact prefixLift 2839273
  have htrace : WordTrace (prefixWord ++ tailWord_2839273) baseStart_2839273 baseEnd_2839273 := by
    simpa [prefixWord, tailWord_2839273, baseEnd_2839273] using wordTrace_append hprefix tailTrace_2839273
  have hstable : (prefixWord ++ tailWord_2839273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839273).length < 2 ^ (prefixWord ++ tailWord_2839273).sum := by decide
  have hdescent : baseEnd_2839273 < baseStart_2839273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839276 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 4, 7]
def baseStart_2839276 : Nat := 118140960795 + 2839276 * 2 ^ 59
def prefixEnd_2839276 : Nat := 4983230072969 + 3 ^ 40 * 2839276 * 2
def baseEnd_2839276 : Nat := 485971099591712851097471

theorem tailTrace_2839276 : CollatzResearch.WordTrace tailWord_2839276 prefixEnd_2839276 485971099591712851097471 := by
  unfold tailWord_2839276
  simp only [CollatzResearch.WordTrace]
  refine ⟨51778451630897718290136841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69037935507863624386849121 51778451630897718290136841)
  ·
    refine ⟨38833838723173288717602631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51778451630897718290136841 38833838723173288717602631)
    ·
      refine ⟨58250758084759933076403947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38833838723173288717602631 58250758084759933076403947)
      ·
        refine ⟨87376137127139899614605921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58250758084759933076403947 87376137127139899614605921)
        ·
          refine ⟨65532102845354924710954441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87376137127139899614605921 65532102845354924710954441)
          ·
            refine ⟨49149077134016193533215831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65532102845354924710954441 49149077134016193533215831)
            ·
              refine ⟨73723615701024290299823747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49149077134016193533215831 73723615701024290299823747)
              ·
                refine ⟨110585423551536435449735621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73723615701024290299823747 110585423551536435449735621)
                ·
                  refine ⟨20734766915913081646825429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110585423551536435449735621 20734766915913081646825429)
                  ·
                    refine ⟨485971099591712851097471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20734766915913081646825429 485971099591712851097471)
                    ·
                      rfl

theorem cell23_2839276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_2839276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839276 prefixEnd_2839276 := by exact prefixLift 2839276
  have htrace : WordTrace (prefixWord ++ tailWord_2839276) baseStart_2839276 baseEnd_2839276 := by
    simpa [prefixWord, tailWord_2839276, baseEnd_2839276] using wordTrace_append hprefix tailTrace_2839276
  have hstable : (prefixWord ++ tailWord_2839276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839276).length < 2 ^ (prefixWord ++ tailWord_2839276).sum := by decide
  have hdescent : baseEnd_2839276 < baseStart_2839276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839294 : List Nat := [4, 2, 2, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_2839294 : Nat := 118140960795 + 2839294 * 2 ^ 59
def prefixEnd_2839294 : Nat := 4983230072969 + 3 ^ 40 * 2839294 * 2
def baseEnd_2839294 : Nat := 1457922541426919482867331

theorem tailTrace_2839294 : CollatzResearch.WordTrace tailWord_2839294 prefixEnd_2839294 1457922541426919482867331 := by
  unfold tailWord_2839294
  simp only [CollatzResearch.WordTrace]
  refine ⟨12944694971966278206803617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69038373183820150436285957 12944694971966278206803617)
  ·
    refine ⟨9708521228974708655102713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12944694971966278206803617 9708521228974708655102713)
    ·
      refine ⟨7281390921731031491327035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9708521228974708655102713 7281390921731031491327035)
      ·
        refine ⟨10922086382596547236990553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7281390921731031491327035 10922086382596547236990553)
        ·
          refine ⟨8191564786947410427742915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10922086382596547236990553 8191564786947410427742915)
          ·
            refine ⟨12287347180421115641614373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8191564786947410427742915 12287347180421115641614373)
            ·
              refine ⟨2303877596328959182802695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12287347180421115641614373 2303877596328959182802695)
              ·
                refine ⟨3455816394493438774204043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303877596328959182802695 3455816394493438774204043)
                ·
                  refine ⟨5183724591740158161306065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3455816394493438774204043 5183724591740158161306065)
                  ·
                    refine ⟨3887793443805118620979549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5183724591740158161306065 3887793443805118620979549)
                    ·
                      refine ⟨1457922541426919482867331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3887793443805118620979549 1457922541426919482867331)
                      ·
                        rfl

theorem cell23_2839294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_2839294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839294 prefixEnd_2839294 := by exact prefixLift 2839294
  have htrace : WordTrace (prefixWord ++ tailWord_2839294) baseStart_2839294 baseEnd_2839294 := by
    simpa [prefixWord, tailWord_2839294, baseEnd_2839294] using wordTrace_append hprefix tailTrace_2839294
  have hstable : (prefixWord ++ tailWord_2839294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839294).length < 2 ^ (prefixWord ++ tailWord_2839294).sum := by decide
  have hdescent : baseEnd_2839294 < baseStart_2839294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839324 : List Nat := [2, 2, 3, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_2839324 : Nat := 118140960795 + 2839324 * 2 ^ 59
def prefixEnd_2839324 : Nat := 4983230072969 + 3 ^ 40 * 2839324 * 2
def baseEnd_2839324 : Nat := 1457937945846554365492193

theorem tailTrace_2839324 : CollatzResearch.WordTrace tailWord_2839324 prefixEnd_2839324 1457937945846554365492193 := by
  unfold tailWord_2839324
  simp only [CollatzResearch.WordTrace]
  refine ⟨51779326982810770389010513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69039102643747693852014017 51779326982810770389010513)
  ·
    refine ⟨38834495237108077791757885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51779326982810770389010513 38834495237108077791757885)
    ·
      refine ⟨14562935713915529171909207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38834495237108077791757885 14562935713915529171909207)
      ·
        refine ⟨21844403570873293757863811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14562935713915529171909207 21844403570873293757863811)
        ·
          refine ⟨32766605356309940636795717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21844403570873293757863811 32766605356309940636795717)
          ·
            refine ⟨6143738504308113869399197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32766605356309940636795717 6143738504308113869399197)
            ·
              refine ⟨2303901939115542701024699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6143738504308113869399197 2303901939115542701024699)
              ·
                refine ⟨3455852908673314051537049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303901939115542701024699 3455852908673314051537049)
                ·
                  refine ⟨2591889681504985538652787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3455852908673314051537049 2591889681504985538652787)
                  ·
                    refine ⟨3887834522257478307979181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2591889681504985538652787 3887834522257478307979181)
                    ·
                      refine ⟨1457937945846554365492193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3887834522257478307979181 1457937945846554365492193)
                      ·
                        rfl

theorem cell23_2839324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_2839324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839324 prefixEnd_2839324 := by exact prefixLift 2839324
  have htrace : WordTrace (prefixWord ++ tailWord_2839324) baseStart_2839324 baseEnd_2839324 := by
    simpa [prefixWord, tailWord_2839324, baseEnd_2839324] using wordTrace_append hprefix tailTrace_2839324
  have hstable : (prefixWord ++ tailWord_2839324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839324).length < 2 ^ (prefixWord ++ tailWord_2839324).sum := by decide
  have hdescent : baseEnd_2839324 < baseStart_2839324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839333 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_2839333 : Nat := 118140960795 + 2839333 * 2 ^ 59
def prefixEnd_2839333 : Nat := 4983230072969 + 3 ^ 40 * 2839333 * 2
def baseEnd_2839333 : Nat := 1457942567172444830279651

theorem tailTrace_2839333 : CollatzResearch.WordTrace tailWord_2839333 prefixEnd_2839333 1457942567172444830279651 := by
  unfold tailWord_2839333
  simp only [CollatzResearch.WordTrace]
  refine ⟨103558982222588935315098653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69039321481725956876732435 103558982222588935315098653)
  ·
    refine ⟨38834618333470850743161995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103558982222588935315098653 38834618333470850743161995)
    ·
      refine ⟨58251927500206276114742993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38834618333470850743161995 58251927500206276114742993)
      ·
        refine ⟨43688945625154707086057245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58251927500206276114742993 43688945625154707086057245)
        ·
          refine ⟨16383354609433015157271467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43688945625154707086057245 16383354609433015157271467)
          ·
            refine ⟨24575031914149522735907201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16383354609433015157271467 24575031914149522735907201)
            ·
              refine ⟨18431273935612142051930401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24575031914149522735907201 18431273935612142051930401)
              ·
                refine ⟨13823455451709106538947801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18431273935612142051930401 13823455451709106538947801)
                ·
                  refine ⟨10367591588781829904210851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13823455451709106538947801 10367591588781829904210851)
                  ·
                    refine ⟨15551387383172744856316277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10367591588781829904210851 15551387383172744856316277)
                    ·
                      refine ⟨1457942567172444830279651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15551387383172744856316277 1457942567172444830279651)
                      ·
                        rfl

theorem cell23_2839333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_2839333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839333 prefixEnd_2839333 := by exact prefixLift 2839333
  have htrace : WordTrace (prefixWord ++ tailWord_2839333) baseStart_2839333 baseEnd_2839333 := by
    simpa [prefixWord, tailWord_2839333, baseEnd_2839333] using wordTrace_append hprefix tailTrace_2839333
  have hstable : (prefixWord ++ tailWord_2839333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839333).length < 2 ^ (prefixWord ++ tailWord_2839333).sum := by decide
  have hdescent : baseEnd_2839333 < baseStart_2839333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839347 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 4, 2, 2]
def baseStart_2839347 : Nat := 118140960795 + 2839347 * 2 ^ 59
def prefixEnd_2839347 : Nat := 4983230072969 + 3 ^ 40 * 2839347 * 2
def baseEnd_2839347 : Nat := 1457949755901607775504587

theorem tailTrace_2839347 : CollatzResearch.WordTrace tailWord_2839347 prefixEnd_2839347 1457949755901607775504587 := by
  unfold tailWord_2839347
  simp only [CollatzResearch.WordTrace]
  refine ⟨103559492844538215706108295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69039661896358810470738863 103559492844538215706108295)
  ·
    refine ⟨155339239266807323559162443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103559492844538215706108295 155339239266807323559162443)
    ·
      refine ⟨233008858900210985338743665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155339239266807323559162443 233008858900210985338743665)
      ·
        refine ⟨174756644175158239004057749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233008858900210985338743665 174756644175158239004057749)
        ·
          refine ⟨8191717695710542453315207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 174756644175158239004057749 8191717695710542453315207)
          ·
            refine ⟨12287576543565813679972811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8191717695710542453315207 12287576543565813679972811)
            ·
              refine ⟨18431364815348720519959217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12287576543565813679972811 18431364815348720519959217)
              ·
                refine ⟨13823523611511540389969413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18431364815348720519959217 13823523611511540389969413)
                ·
                  refine ⟨2591910677158413823119265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13823523611511540389969413 2591910677158413823119265)
                  ·
                    refine ⟨1943933007868810367339449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2591910677158413823119265 1943933007868810367339449)
                    ·
                      refine ⟨1457949755901607775504587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1943933007868810367339449 1457949755901607775504587)
                      ·
                        rfl

theorem cell23_2839347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 2, 2].length) (baseStart_2839347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839347 prefixEnd_2839347 := by exact prefixLift 2839347
  have htrace : WordTrace (prefixWord ++ tailWord_2839347) baseStart_2839347 baseEnd_2839347 := by
    simpa [prefixWord, tailWord_2839347, baseEnd_2839347] using wordTrace_append hprefix tailTrace_2839347
  have hstable : (prefixWord ++ tailWord_2839347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839347).length < 2 ^ (prefixWord ++ tailWord_2839347).sum := by decide
  have hdescent : baseEnd_2839347 < baseStart_2839347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839400 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 2, 5]
def baseStart_2839400 : Nat := 118140960795 + 2839400 * 2 ^ 59
def prefixEnd_2839400 : Nat := 4983230072969 + 3 ^ 40 * 2839400 * 2
def baseEnd_2839400 : Nat := 485992323458765356047281

theorem tailTrace_2839400 : CollatzResearch.WordTrace tailWord_2839400 prefixEnd_2839400 485992323458765356047281 := by
  unfold tailWord_2839400
  simp only [CollatzResearch.WordTrace]
  refine ⟨51780712956673102878893827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69040950608897470505191769 51780712956673102878893827)
  ·
    refine ⟨77671069435009654318340741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51780712956673102878893827 77671069435009654318340741)
    ·
      refine ⟨14563325519064310184688889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77671069435009654318340741 14563325519064310184688889)
      ·
        refine ⟨10922494139298232638516667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14563325519064310184688889 10922494139298232638516667)
        ·
          refine ⟨16383741208947348957775001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10922494139298232638516667 16383741208947348957775001)
          ·
            refine ⟨12287805906710511718331251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16383741208947348957775001 12287805906710511718331251)
            ·
              refine ⟨18431708860065767577496877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12287805906710511718331251 18431708860065767577496877)
              ·
                refine ⟨6911890822524662841561329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18431708860065767577496877 6911890822524662841561329)
                ·
                  refine ⟨5183918116893497131170997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6911890822524662841561329 5183918116893497131170997)
                  ·
                    refine ⟨485992323458765356047281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5183918116893497131170997 485992323458765356047281)
                    ·
                      rfl

theorem cell23_2839400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_2839400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839400 prefixEnd_2839400 := by exact prefixLift 2839400
  have htrace : WordTrace (prefixWord ++ tailWord_2839400) baseStart_2839400 baseEnd_2839400 := by
    simpa [prefixWord, tailWord_2839400, baseEnd_2839400] using wordTrace_append hprefix tailTrace_2839400
  have hstable : (prefixWord ++ tailWord_2839400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839400).length < 2 ^ (prefixWord ++ tailWord_2839400).sum := by decide
  have hdescent : baseEnd_2839400 < baseStart_2839400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839403 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 4]
def baseStart_2839403 : Nat := 118140960795 + 2839403 * 2 ^ 59
def prefixEnd_2839403 : Nat := 4983230072969 + 3 ^ 40 * 2839403 * 2
def baseEnd_2839403 : Nat := 1457978510818259556404329

theorem tailTrace_2839403 : CollatzResearch.WordTrace tailWord_2839403 prefixEnd_2839403 1457978510818259556404329 := by
  unfold tailWord_2839403
  simp only [CollatzResearch.WordTrace]
  refine ⟨103561535332335337270146863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69041023554890224846764575 103561535332335337270146863)
  ·
    refine ⟨155342302998503005905220295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103561535332335337270146863 155342302998503005905220295)
    ·
      refine ⟨233013454497754508857830443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155342302998503005905220295 233013454497754508857830443)
      ·
        refine ⟨349520181746631763286745665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233013454497754508857830443 349520181746631763286745665)
        ·
          refine ⟨262140136309973822465059249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349520181746631763286745665 262140136309973822465059249)
          ·
            refine ⟨196605102232480366848794437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262140136309973822465059249 196605102232480366848794437)
            ·
              refine ⟨36863456668590068784148957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196605102232480366848794437 36863456668590068784148957)
              ·
                refine ⟨13823796250721275794055859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36863456668590068784148957 13823796250721275794055859)
                ·
                  refine ⟨20735694376081913691083789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13823796250721275794055859 20735694376081913691083789)
                  ·
                    refine ⟨7775885391030717634156421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20735694376081913691083789 7775885391030717634156421)
                    ·
                      refine ⟨1457978510818259556404329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7775885391030717634156421 1457978510818259556404329)
                      ·
                        rfl

theorem cell23_2839403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 4].length) (baseStart_2839403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839403 prefixEnd_2839403 := by exact prefixLift 2839403
  have htrace : WordTrace (prefixWord ++ tailWord_2839403) baseStart_2839403 baseEnd_2839403 := by
    simpa [prefixWord, tailWord_2839403, baseEnd_2839403] using wordTrace_append hprefix tailTrace_2839403
  have hstable : (prefixWord ++ tailWord_2839403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839403).length < 2 ^ (prefixWord ++ tailWord_2839403).sum := by decide
  have hdescent : baseEnd_2839403 < baseStart_2839403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839420 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 3, 6, 2]
def baseStart_2839420 : Nat := 118140960795 + 2839420 * 2 ^ 59
def prefixEnd_2839420 : Nat := 4983230072969 + 3 ^ 40 * 2839420 * 2
def baseEnd_2839420 : Nat := 1457987239989385989891751

theorem tailTrace_2839420 : CollatzResearch.WordTrace tailWord_2839420 prefixEnd_2839420 1457987239989385989891751 := by
  unfold tailWord_2839420
  simp only [CollatzResearch.WordTrace]
  refine ⟨51781077686636874586757857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69041436915515832782343809 51781077686636874586757857)
  ·
    refine ⟨38835808264977655940068393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51781077686636874586757857 38835808264977655940068393)
    ·
      refine ⟨29126856198733241955051295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38835808264977655940068393 29126856198733241955051295)
      ·
        refine ⟨43690284298099862932576943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29126856198733241955051295 43690284298099862932576943)
        ·
          refine ⟨65535426447149794398865415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43690284298099862932576943 65535426447149794398865415)
          ·
            refine ⟨98303139670724691598298123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65535426447149794398865415 98303139670724691598298123)
            ·
              refine ⟨147454709506087037397447185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98303139670724691598298123 147454709506087037397447185)
              ·
                refine ⟨110591032129565278048085389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147454709506087037397447185 110591032129565278048085389)
                ·
                  refine ⟨41471637048586979268032021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110591032129565278048085389 41471637048586979268032021)
                  ·
                    refine ⟨1943982986652514653189001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41471637048586979268032021 1943982986652514653189001)
                    ·
                      refine ⟨1457987239989385989891751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1943982986652514653189001 1457987239989385989891751)
                      ·
                        rfl

theorem cell23_2839420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_2839420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839420 prefixEnd_2839420 := by exact prefixLift 2839420
  have htrace : WordTrace (prefixWord ++ tailWord_2839420) baseStart_2839420 baseEnd_2839420 := by
    simpa [prefixWord, tailWord_2839420, baseEnd_2839420] using wordTrace_append hprefix tailTrace_2839420
  have hstable : (prefixWord ++ tailWord_2839420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839420).length < 2 ^ (prefixWord ++ tailWord_2839420).sum := by decide
  have hdescent : baseEnd_2839420 < baseStart_2839420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839457 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2839457 : Nat := 118140960795 + 2839457 * 2 ^ 59
def prefixEnd_2839457 : Nat := 4983230072969 + 3 ^ 40 * 2839457 * 2
def baseEnd_2839457 : Nat := 1458006238773602345129081

theorem tailTrace_2839457 : CollatzResearch.WordTrace tailWord_2839457 prefixEnd_2839457 1458006238773602345129081 := by
  unfold tailWord_2839457
  simp only [CollatzResearch.WordTrace]
  refine ⟨103563504874139704492612625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69042336582759802995075083 103563504874139704492612625)
  ·
    refine ⟨77672628655604778369459469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103563504874139704492612625 77672628655604778369459469)
    ·
      refine ⟨29127235745851791888547301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77672628655604778369459469 29127235745851791888547301)
      ·
        refine ⟨5461356702347210979102619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29127235745851791888547301 5461356702347210979102619)
        ·
          refine ⟨8192035053520816468653929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5461356702347210979102619 8192035053520816468653929)
          ·
            refine ⟨6144026290140612351490447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8192035053520816468653929 6144026290140612351490447)
            ·
              refine ⟨9216039435210918527235671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6144026290140612351490447 9216039435210918527235671)
              ·
                refine ⟨13824059152816377790853507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9216039435210918527235671 13824059152816377790853507)
                ·
                  refine ⟨20736088729224566686280261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13824059152816377790853507 20736088729224566686280261)
                  ·
                    refine ⟨3888016636729606253677549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20736088729224566686280261 3888016636729606253677549)
                    ·
                      refine ⟨1458006238773602345129081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3888016636729606253677549 1458006238773602345129081)
                      ·
                        rfl

theorem cell23_2839457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2839457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839457 prefixEnd_2839457 := by exact prefixLift 2839457
  have htrace : WordTrace (prefixWord ++ tailWord_2839457) baseStart_2839457 baseEnd_2839457 := by
    simpa [prefixWord, tailWord_2839457, baseEnd_2839457] using wordTrace_append hprefix tailTrace_2839457
  have hstable : (prefixWord ++ tailWord_2839457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839457).length < 2 ^ (prefixWord ++ tailWord_2839457).sum := by decide
  have hdescent : baseEnd_2839457 < baseStart_2839457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839537 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 4, 4]
def baseStart_2839537 : Nat := 118140960795 + 2839537 * 2 ^ 59
def prefixEnd_2839537 : Nat := 4983230072969 + 3 ^ 40 * 2839537 * 2
def baseEnd_2839537 : Nat := 486015772408654010709571

theorem tailTrace_2839537 : CollatzResearch.WordTrace tailWord_2839537 prefixEnd_2839537 486015772408654010709571 := by
  unfold tailWord_2839537
  simp only [CollatzResearch.WordTrace]
  refine ⟨103566422713849878155524865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69044281809233252103683243 103566422713849878155524865)
  ·
    refine ⟨77674817035387408616643649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103566422713849878155524865 77674817035387408616643649)
    ·
      refine ⟨58256112776540556462482737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77674817035387408616643649 58256112776540556462482737)
      ·
        refine ⟨43692084582405417346862053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58256112776540556462482737 43692084582405417346862053)
        ·
          refine ⟨8192265859201015752536635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43692084582405417346862053 8192265859201015752536635)
          ·
            refine ⟨12288398788801523628804953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8192265859201015752536635 12288398788801523628804953)
            ·
              refine ⟨9216299091601142721603715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12288398788801523628804953 9216299091601142721603715)
              ·
                refine ⟨13824448637401714082405573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9216299091601142721603715 13824448637401714082405573)
                ·
                  refine ⟨2592084119512821390451045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13824448637401714082405573 2592084119512821390451045)
                  ·
                    refine ⟨486015772408654010709571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2592084119512821390451045 486015772408654010709571)
                    ·
                      rfl

theorem cell23_2839537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_2839537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839537 prefixEnd_2839537 := by exact prefixLift 2839537
  have htrace : WordTrace (prefixWord ++ tailWord_2839537) baseStart_2839537 baseEnd_2839537 := by
    simpa [prefixWord, tailWord_2839537, baseEnd_2839537] using wordTrace_append hprefix tailTrace_2839537
  have hstable : (prefixWord ++ tailWord_2839537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839537).length < 2 ^ (prefixWord ++ tailWord_2839537).sum := by decide
  have hdescent : baseEnd_2839537 < baseStart_2839537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839538 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2839538 : Nat := 118140960795 + 2839538 * 2 ^ 59
def prefixEnd_2839538 : Nat := 4983230072969 + 3 ^ 40 * 2839538 * 2
def baseEnd_2839538 : Nat := 1458047830706616528216209

theorem tailTrace_2839538 : CollatzResearch.WordTrace tailWord_2839538 prefixEnd_2839538 1458047830706616528216209 := by
  unfold tailWord_2839538
  simp only [CollatzResearch.WordTrace]
  refine ⟨25891614796711563831577817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69044306124564170217540845 25891614796711563831577817)
  ·
    refine ⟨19418711097533672873683363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25891614796711563831577817 19418711097533672873683363)
    ·
      refine ⟨29128066646300509310525045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19418711097533672873683363 29128066646300509310525045)
      ·
        refine ⟨2730756248090672747861723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29128066646300509310525045 2730756248090672747861723)
        ·
          refine ⟨4096134372136009121792585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2730756248090672747861723 4096134372136009121792585)
          ·
            refine ⟨3072100779102006841344439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4096134372136009121792585 3072100779102006841344439)
            ·
              refine ⟨4608151168653010262016659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072100779102006841344439 4608151168653010262016659)
              ·
                refine ⟨6912226752979515393024989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4608151168653010262016659 6912226752979515393024989)
                ·
                  refine ⟨2592085032367318272384371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6912226752979515393024989 2592085032367318272384371)
                  ·
                    refine ⟨3888127548550977408576557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2592085032367318272384371 3888127548550977408576557)
                    ·
                      refine ⟨1458047830706616528216209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3888127548550977408576557 1458047830706616528216209)
                      ·
                        rfl

theorem cell23_2839538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2839538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839538 prefixEnd_2839538 := by exact prefixLift 2839538
  have htrace : WordTrace (prefixWord ++ tailWord_2839538) baseStart_2839538 baseEnd_2839538 := by
    simpa [prefixWord, tailWord_2839538, baseEnd_2839538] using wordTrace_append hprefix tailTrace_2839538
  have hstable : (prefixWord ++ tailWord_2839538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839538).length < 2 ^ (prefixWord ++ tailWord_2839538).sum := by decide
  have hdescent : baseEnd_2839538 < baseStart_2839538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839564 : List Nat := [2, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3]
def baseStart_2839564 : Nat := 118140960795 + 2839564 * 2 ^ 59
def prefixEnd_2839564 : Nat := 4983230072969 + 3 ^ 40 * 2839564 * 2
def baseEnd_2839564 : Nat := 1458061181203633426491089

theorem tailTrace_2839564 : CollatzResearch.WordTrace tailWord_2839564 prefixEnd_2839564 1458061181203633426491089 := by
  unfold tailWord_2839564
  simp only [CollatzResearch.WordTrace]
  refine ⟨51783703742376030883378873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69044938323168041177838497 51783703742376030883378873)
  ·
    refine ⟨38837777806782023162534155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51783703742376030883378873 38837777806782023162534155)
    ·
      refine ⟨58256666710173034743801233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38837777806782023162534155 58256666710173034743801233)
      ·
        refine ⟨43692500032629776057850925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58256666710173034743801233 43692500032629776057850925)
        ·
          refine ⟨16384687512236166021694097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43692500032629776057850925 16384687512236166021694097)
          ·
            refine ⟨12288515634177124516270573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16384687512236166021694097 12288515634177124516270573)
            ·
              refine ⟨4608193362816421693601465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12288515634177124516270573 4608193362816421693601465)
              ·
                refine ⟨3456145022112316270201099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4608193362816421693601465 3456145022112316270201099)
                ·
                  refine ⟨5184217533168474405301649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456145022112316270201099 5184217533168474405301649)
                  ·
                    refine ⟨3888163149876355803976237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5184217533168474405301649 3888163149876355803976237)
                    ·
                      refine ⟨1458061181203633426491089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3888163149876355803976237 1458061181203633426491089)
                      ·
                        rfl

theorem cell23_2839564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_2839564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839564 prefixEnd_2839564 := by exact prefixLift 2839564
  have htrace : WordTrace (prefixWord ++ tailWord_2839564) baseStart_2839564 baseEnd_2839564 := by
    simpa [prefixWord, tailWord_2839564, baseEnd_2839564] using wordTrace_append hprefix tailTrace_2839564
  have hstable : (prefixWord ++ tailWord_2839564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839564).length < 2 ^ (prefixWord ++ tailWord_2839564).sum := by decide
  have hdescent : baseEnd_2839564 < baseStart_2839564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839577 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 6, 1, 3]
def baseStart_2839577 : Nat := 118140960795 + 2839577 * 2 ^ 59
def prefixEnd_2839577 : Nat := 4983230072969 + 3 ^ 40 * 2839577 * 2
def baseEnd_2839577 : Nat := 1458067856452141875628529

theorem tailTrace_2839577 : CollatzResearch.WordTrace tailWord_2839577 prefixEnd_2839577 1458067856452141875628529 := by
  unfold tailWord_2839577
  simp only [CollatzResearch.WordTrace]
  refine ⟨103567881633704964986980985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69045254422469976657987323 103567881633704964986980985)
  ·
    refine ⟨77675911225278723740235739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103567881633704964986980985 77675911225278723740235739)
    ·
      refine ⟨116513866837918085610353609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77675911225278723740235739 116513866837918085610353609)
      ·
        refine ⟨87385400128438564207765207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116513866837918085610353609 87385400128438564207765207)
        ·
          refine ⟨131078100192657846311647811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87385400128438564207765207 131078100192657846311647811)
          ·
            refine ⟨196617150288986769467471717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131078100192657846311647811 196617150288986769467471717)
            ·
              refine ⟨36865715679185019275150947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196617150288986769467471717 36865715679185019275150947)
              ·
                refine ⟨55298573518777528912726421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36865715679185019275150947 55298573518777528912726421)
                ·
                  refine ⟨2592120633692696667784051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55298573518777528912726421 2592120633692696667784051)
                  ·
                    refine ⟨3888180950539045001676077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2592120633692696667784051 3888180950539045001676077)
                    ·
                      refine ⟨1458067856452141875628529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3888180950539045001676077 1458067856452141875628529)
                      ·
                        rfl

theorem cell23_2839577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_2839577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839577 prefixEnd_2839577 := by exact prefixLift 2839577
  have htrace : WordTrace (prefixWord ++ tailWord_2839577) baseStart_2839577 baseEnd_2839577 := by
    simpa [prefixWord, tailWord_2839577, baseEnd_2839577] using wordTrace_append hprefix tailTrace_2839577
  have hstable : (prefixWord ++ tailWord_2839577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839577).length < 2 ^ (prefixWord ++ tailWord_2839577).sum := by decide
  have hdescent : baseEnd_2839577 < baseStart_2839577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839581 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_2839581 : Nat := 118140960795 + 2839581 * 2 ^ 59
def prefixEnd_2839581 : Nat := 4983230072969 + 3 ^ 40 * 2839581 * 2
def baseEnd_2839581 : Nat := 1458069910374759859978511

theorem tailTrace_2839581 : CollatzResearch.WordTrace tailWord_2839581 prefixEnd_2839581 1458069910374759859978511 := by
  unfold tailWord_2839581
  simp only [CollatzResearch.WordTrace]
  refine ⟨103568027525690473670126597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69045351683793649113417731 103568027525690473670126597)
  ·
    refine ⟨19419005161066963813148737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103568027525690473670126597 19419005161066963813148737)
    ·
      refine ⟨14564253870800222859861553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19419005161066963813148737 14564253870800222859861553)
      ·
        refine ⟨10923190403100167144896165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14564253870800222859861553 10923190403100167144896165)
        ·
          refine ⟨2048098200581281339668031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10923190403100167144896165 2048098200581281339668031)
          ·
            refine ⟨3072147300871922009502047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048098200581281339668031 3072147300871922009502047)
            ·
              refine ⟨4608220951307883014253071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072147300871922009502047 4608220951307883014253071)
              ·
                refine ⟨6912331426961824521379607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4608220951307883014253071 6912331426961824521379607)
                ·
                  refine ⟨10368497140442736782069411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6912331426961824521379607 10368497140442736782069411)
                  ·
                    refine ⟨15552745710664105173104117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10368497140442736782069411 15552745710664105173104117)
                    ·
                      refine ⟨1458069910374759859978511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15552745710664105173104117 1458069910374759859978511)
                      ·
                        rfl

theorem cell23_2839581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_2839581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839581 prefixEnd_2839581 := by exact prefixLift 2839581
  have htrace : WordTrace (prefixWord ++ tailWord_2839581) baseStart_2839581 baseEnd_2839581 := by
    simpa [prefixWord, tailWord_2839581, baseEnd_2839581] using wordTrace_append hprefix tailTrace_2839581
  have hstable : (prefixWord ++ tailWord_2839581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839581).length < 2 ^ (prefixWord ++ tailWord_2839581).sum := by decide
  have hdescent : baseEnd_2839581 < baseStart_2839581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839600 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 4]
def baseStart_2839600 : Nat := 118140960795 + 2839600 * 2 ^ 59
def prefixEnd_2839600 : Nat := 4983230072969 + 3 ^ 40 * 2839600 * 2
def baseEnd_2839600 : Nat := 1458079666507195285640923

theorem tailTrace_2839600 : CollatzResearch.WordTrace tailWord_2839600 prefixEnd_2839600 1458079666507195285640923 := by
  unfold tailWord_2839600
  simp only [CollatzResearch.WordTrace]
  refine ⟨51784360256310819957534127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69045813675081093276712169 51784360256310819957534127)
  ·
    refine ⟨77676540384466229936301191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51784360256310819957534127 77676540384466229936301191)
    ·
      refine ⟨116514810576699344904451787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77676540384466229936301191 116514810576699344904451787)
      ·
        refine ⟨174772215865049017356677681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116514810576699344904451787 174772215865049017356677681)
        ·
          refine ⟨131079161898786763017508261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174772215865049017356677681 131079161898786763017508261)
          ·
            refine ⟨24577342856022518065782799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131079161898786763017508261 24577342856022518065782799)
            ·
              refine ⟨36866014284033777098674199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24577342856022518065782799 36866014284033777098674199)
              ·
                refine ⟨55299021426050665648011299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36866014284033777098674199 55299021426050665648011299)
                ·
                  refine ⟨82948532139075998472016949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55299021426050665648011299 82948532139075998472016949)
                  ·
                    refine ⟨7776424888038374856751589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82948532139075998472016949 7776424888038374856751589)
                    ·
                      refine ⟨1458079666507195285640923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7776424888038374856751589 1458079666507195285640923)
                      ·
                        rfl

theorem cell23_2839600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_2839600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839600 prefixEnd_2839600 := by exact prefixLift 2839600
  have htrace : WordTrace (prefixWord ++ tailWord_2839600) baseStart_2839600 baseEnd_2839600 := by
    simpa [prefixWord, tailWord_2839600, baseEnd_2839600] using wordTrace_append hprefix tailTrace_2839600
  have hstable : (prefixWord ++ tailWord_2839600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839600).length < 2 ^ (prefixWord ++ tailWord_2839600).sum := by decide
  have hdescent : baseEnd_2839600 < baseStart_2839600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839610 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 1, 8]
def baseStart_2839610 : Nat := 118140960795 + 2839610 * 2 ^ 59
def prefixEnd_2839610 : Nat := 4983230072969 + 3 ^ 40 * 2839610 * 2
def baseEnd_2839610 : Nat := 486028267104580082171959

theorem tailTrace_2839610 : CollatzResearch.WordTrace tailWord_2839610 prefixEnd_2839610 486028267104580082171959 := by
  unfold tailWord_2839610
  simp only [CollatzResearch.WordTrace]
  refine ⟨25892271310646352905733071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69046056828390274415288189 25892271310646352905733071)
  ·
    refine ⟨38838406965969529358599607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25892271310646352905733071 38838406965969529358599607)
    ·
      refine ⟨58257610448954294037899411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38838406965969529358599607 58257610448954294037899411)
      ·
        refine ⟨87386415673431441056849117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58257610448954294037899411 87386415673431441056849117)
        ·
          refine ⟨32769905877536790396318419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87386415673431441056849117 32769905877536790396318419)
          ·
            refine ⟨49154858816305185594477629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32769905877536790396318419 49154858816305185594477629)
            ·
              refine ⟨18433072056114444597929111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49154858816305185594477629 18433072056114444597929111)
              ·
                refine ⟨27649608084171666896893667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18433072056114444597929111 27649608084171666896893667)
                ·
                  refine ⟨41474412126257500345340501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27649608084171666896893667 41474412126257500345340501)
                  ·
                    refine ⟨486028267104580082171959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41474412126257500345340501 486028267104580082171959)
                    ·
                      rfl

theorem cell23_2839610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_2839610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839610 prefixEnd_2839610 := by exact prefixLift 2839610
  have htrace : WordTrace (prefixWord ++ tailWord_2839610) baseStart_2839610 baseEnd_2839610 := by
    simpa [prefixWord, tailWord_2839610, baseEnd_2839610] using wordTrace_append hprefix tailTrace_2839610
  have hstable : (prefixWord ++ tailWord_2839610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839610).length < 2 ^ (prefixWord ++ tailWord_2839610).sum := by decide
  have hdescent : baseEnd_2839610 < baseStart_2839610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839640 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 9]
def baseStart_2839640 : Nat := 118140960795 + 2839640 * 2 ^ 59
def prefixEnd_2839640 : Nat := 4983230072969 + 3 ^ 40 * 2839640 * 2
def baseEnd_2839640 : Nat := 162011133970375014348971

theorem tailTrace_2839640 : CollatzResearch.WordTrace tailWord_2839640 prefixEnd_2839640 162011133970375014348971 := by
  unfold tailWord_2839640
  simp only [CollatzResearch.WordTrace]
  refine ⟨51785089716238363373262187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69046786288317817831016249 51785089716238363373262187)
  ·
    refine ⟨77677634574357545059893281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51785089716238363373262187 77677634574357545059893281)
    ·
      refine ⟨58258225930768158794919961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77677634574357545059893281 58258225930768158794919961)
      ·
        refine ⟨43693669448076119096189971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58258225930768158794919961 43693669448076119096189971)
        ·
          refine ⟨65540504172114178644284957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43693669448076119096189971 65540504172114178644284957)
          ·
            refine ⟨24577689064542816991606859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65540504172114178644284957 24577689064542816991606859)
            ·
              refine ⟨36866533596814225487410289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24577689064542816991606859 36866533596814225487410289)
              ·
                refine ⟨27649900197610669115557717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36866533596814225487410289 27649900197610669115557717)
                ·
                  refine ⟨162011133970375014348971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27649900197610669115557717 162011133970375014348971)
                  ·
                    rfl

theorem cell23_2839640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 9].length) (baseStart_2839640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839640 prefixEnd_2839640 := by exact prefixLift 2839640
  have htrace : WordTrace (prefixWord ++ tailWord_2839640) baseStart_2839640 baseEnd_2839640 := by
    simpa [prefixWord, tailWord_2839640, baseEnd_2839640] using wordTrace_append hprefix tailTrace_2839640
  have hstable : (prefixWord ++ tailWord_2839640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839640).length < 2 ^ (prefixWord ++ tailWord_2839640).sum := by decide
  have hdescent : baseEnd_2839640 < baseStart_2839640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839645 : List Nat := [1, 4, 4, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2839645 : Nat := 118140960795 + 2839645 * 2 ^ 59
def prefixEnd_2839645 : Nat := 4983230072969 + 3 ^ 40 * 2839645 * 2
def baseEnd_2839645 : Nat := 1458102773136647609578217

theorem tailTrace_2839645 : CollatzResearch.WordTrace tailWord_2839645 prefixEnd_2839645 1458102773136647609578217 := by
  unfold tailWord_2839645
  simp only [CollatzResearch.WordTrace]
  refine ⟨103570361797458612600456389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69046907864972408400304259 103570361797458612600456389)
  ·
    refine ⟨19419442837023489862585573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103570361797458612600456389 19419442837023489862585573)
    ·
      refine ⟨3641145531941904349234795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19419442837023489862585573 3641145531941904349234795)
      ·
        refine ⟨5461718297912856523852193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3641145531941904349234795 5461718297912856523852193)
        ·
          refine ⟨4096288723434642392889145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5461718297912856523852193 4096288723434642392889145)
          ·
            refine ⟨3072216542575981794666859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4096288723434642392889145 3072216542575981794666859)
            ·
              refine ⟨4608324813863972692000289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072216542575981794666859 4608324813863972692000289)
              ·
                refine ⟨3456243610397979519000217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4608324813863972692000289 3456243610397979519000217)
                ·
                  refine ⟨2592182707798484639250163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3456243610397979519000217 2592182707798484639250163)
                  ·
                    refine ⟨3888274061697726958875245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2592182707798484639250163 3888274061697726958875245)
                    ·
                      refine ⟨1458102773136647609578217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3888274061697726958875245 1458102773136647609578217)
                      ·
                        rfl

theorem cell23_2839645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2839645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839645 prefixEnd_2839645 := by exact prefixLift 2839645
  have htrace : WordTrace (prefixWord ++ tailWord_2839645) baseStart_2839645 baseEnd_2839645 := by
    simpa [prefixWord, tailWord_2839645, baseEnd_2839645] using wordTrace_append hprefix tailTrace_2839645
  have hstable : (prefixWord ++ tailWord_2839645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839645).length < 2 ^ (prefixWord ++ tailWord_2839645).sum := by decide
  have hdescent : baseEnd_2839645 < baseStart_2839645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839657 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 7]
def baseStart_2839657 : Nat := 118140960795 + 2839657 * 2 ^ 59
def prefixEnd_2839657 : Nat := 4983230072969 + 3 ^ 40 * 2839657 * 2
def baseEnd_2839657 : Nat := 162012103878277951403129

theorem tailTrace_2839657 : CollatzResearch.WordTrace tailWord_2839657 prefixEnd_2839657 162012103878277951403129 := by
  unfold tailWord_2839657
  simp only [CollatzResearch.WordTrace]
  refine ⟨103570799473415138649893225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69047199648943425766595483 103570799473415138649893225)
  ·
    refine ⟨77678099605061353987419919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103570799473415138649893225 77678099605061353987419919)
    ·
      refine ⟨116517149407592030981129879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77678099605061353987419919 116517149407592030981129879)
      ·
        refine ⟨174775724111388046471694819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116517149407592030981129879 174775724111388046471694819)
        ·
          refine ⟨262163586167082069707542229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174775724111388046471694819 262163586167082069707542229)
          ·
            refine ⟨6144459050790986008770521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 262163586167082069707542229 6144459050790986008770521)
            ·
              refine ⟨4608344288093239506577891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6144459050790986008770521 4608344288093239506577891)
              ·
                refine ⟨6912516432139859259866837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4608344288093239506577891 6912516432139859259866837)
                ·
                  refine ⟨162012103878277951403129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6912516432139859259866837 162012103878277951403129)
                  ·
                    rfl

theorem cell23_2839657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 7].length) (baseStart_2839657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839657 prefixEnd_2839657 := by exact prefixLift 2839657
  have htrace : WordTrace (prefixWord ++ tailWord_2839657) baseStart_2839657 baseEnd_2839657 := by
    simpa [prefixWord, tailWord_2839657, baseEnd_2839657] using wordTrace_append hprefix tailTrace_2839657
  have hstable : (prefixWord ++ tailWord_2839657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839657).length < 2 ^ (prefixWord ++ tailWord_2839657).sum := by decide
  have hdescent : baseEnd_2839657 < baseStart_2839657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839687 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 2, 5]
def baseStart_2839687 : Nat := 118140960795 + 2839687 * 2 ^ 59
def prefixEnd_2839687 : Nat := 4983230072969 + 3 ^ 40 * 2839687 * 2
def baseEnd_2839687 : Nat := 486041446441378815084341

theorem tailTrace_2839687 : CollatzResearch.WordTrace tailWord_2839687 prefixEnd_2839687 486041446441378815084341 := by
  unfold tailWord_2839687
  simp only [CollatzResearch.WordTrace]
  refine ⟨103571893663306453773485315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69047929108870969182323543 103571893663306453773485315)
  ·
    refine ⟨155357840494959680660227973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103571893663306453773485315 155357840494959680660227973)
    ·
      refine ⟨29129595092804940123792745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155357840494959680660227973 29129595092804940123792745)
      ·
        refine ⟨21847196319603705092844559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29129595092804940123792745 21847196319603705092844559)
        ·
          refine ⟨32770794479405557639266839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21847196319603705092844559 32770794479405557639266839)
          ·
            refine ⟨49156191719108336458900259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32770794479405557639266839 49156191719108336458900259)
            ·
              refine ⟨73734287578662504688350389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49156191719108336458900259 73734287578662504688350389)
              ·
                refine ⟨6912589460499609814532849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73734287578662504688350389 6912589460499609814532849)
                ·
                  refine ⟨5184442095374707360899637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6912589460499609814532849 5184442095374707360899637)
                  ·
                    refine ⟨486041446441378815084341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5184442095374707360899637 486041446441378815084341)
                    ·
                      rfl

theorem cell23_2839687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_2839687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839687 prefixEnd_2839687 := by exact prefixLift 2839687
  have htrace : WordTrace (prefixWord ++ tailWord_2839687) baseStart_2839687 baseEnd_2839687 := by
    simpa [prefixWord, tailWord_2839687, baseEnd_2839687] using wordTrace_append hprefix tailTrace_2839687
  have hstable : (prefixWord ++ tailWord_2839687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839687).length < 2 ^ (prefixWord ++ tailWord_2839687).sum := by decide
  have hdescent : baseEnd_2839687 < baseStart_2839687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839704 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 2, 5]
def baseStart_2839704 : Nat := 118140960795 + 2839704 * 2 ^ 59
def prefixEnd_2839704 : Nat := 4983230072969 + 3 ^ 40 * 2839704 * 2
def baseEnd_2839704 : Nat := 486044356165087626246815

theorem tailTrace_2839704 : CollatzResearch.WordTrace tailWord_2839704 prefixEnd_2839704 486044356165087626246815 := by
  unfold tailWord_2839704
  simp only [CollatzResearch.WordTrace]
  refine ⟨51786256852122432838427083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69048342469496577117902777 51786256852122432838427083)
  ·
    refine ⟨77679385278183649257640625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51786256852122432838427083 77679385278183649257640625)
    ·
      refine ⟨58259538958637736943230469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77679385278183649257640625 58259538958637736943230469)
      ·
        refine ⟨10923663554744575676855713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58259538958637736943230469 10923663554744575676855713)
        ·
          refine ⟨8192747666058431757641785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10923663554744575676855713 8192747666058431757641785)
          ·
            refine ⟨6144560749543823818231339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8192747666058431757641785 6144560749543823818231339)
            ·
              refine ⟨9216841124315735727347009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6144560749543823818231339 9216841124315735727347009)
              ·
                refine ⟨6912630843236801795510257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9216841124315735727347009 6912630843236801795510257)
                ·
                  refine ⟨5184473132427601346632693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6912630843236801795510257 5184473132427601346632693)
                  ·
                    refine ⟨486044356165087626246815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5184473132427601346632693 486044356165087626246815)
                    ·
                      rfl

theorem cell23_2839704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_2839704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839704 prefixEnd_2839704 := by exact prefixLift 2839704
  have htrace : WordTrace (prefixWord ++ tailWord_2839704) baseStart_2839704 baseEnd_2839704 := by
    simpa [prefixWord, tailWord_2839704, baseEnd_2839704] using wordTrace_append hprefix tailTrace_2839704
  have hstable : (prefixWord ++ tailWord_2839704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839704).length < 2 ^ (prefixWord ++ tailWord_2839704).sum := by decide
  have hdescent : baseEnd_2839704 < baseStart_2839704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839727 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 3]
def baseStart_2839727 : Nat := 118140960795 + 2839727 * 2 ^ 59
def prefixEnd_2839727 : Nat := 4983230072969 + 3 ^ 40 * 2839727 * 2
def baseEnd_2839727 : Nat := 1458144878550316288752839

theorem tailTrace_2839727 : CollatzResearch.WordTrace tailWord_2839727 prefixEnd_2839727 1458144878550316288752839 := by
  unfold tailWord_2839727
  simp only [CollatzResearch.WordTrace]
  refine ⟨103573352583161540604941435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69048901722107693736627623 103573352583161540604941435)
  ·
    refine ⟨155360028874742310907412153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103573352583161540604941435 155360028874742310907412153)
    ·
      refine ⟨116520021656056733180559115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155360028874742310907412153 116520021656056733180559115)
      ·
        refine ⟨174780032484085099770838673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116520021656056733180559115 174780032484085099770838673)
        ·
          refine ⟨131085024363063824828129005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174780032484085099770838673 131085024363063824828129005)
          ·
            refine ⟨49156884136148934310548377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131085024363063824828129005 49156884136148934310548377)
            ·
              refine ⟨36867663102111700732911283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49156884136148934310548377 36867663102111700732911283)
              ·
                refine ⟨55301494653167551099366925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36867663102111700732911283 55301494653167551099366925)
                ·
                  refine ⟨20738060494937831662262597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55301494653167551099366925 20738060494937831662262597)
                  ·
                    refine ⟨3888386342800843436674237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20738060494937831662262597 3888386342800843436674237)
                    ·
                      refine ⟨1458144878550316288752839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3888386342800843436674237 1458144878550316288752839)
                      ·
                        rfl

theorem cell23_2839727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 3].length) (baseStart_2839727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839727 prefixEnd_2839727 := by exact prefixLift 2839727
  have htrace : WordTrace (prefixWord ++ tailWord_2839727) baseStart_2839727 baseEnd_2839727 := by
    simpa [prefixWord, tailWord_2839727, baseEnd_2839727] using wordTrace_append hprefix tailTrace_2839727
  have hstable : (prefixWord ++ tailWord_2839727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839727).length < 2 ^ (prefixWord ++ tailWord_2839727).sum := by decide
  have hdescent : baseEnd_2839727 < baseStart_2839727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839768 : List Nat := [2, 1, 2, 2, 5, 1, 1, 4, 1, 4]
def baseStart_2839768 : Nat := 118140960795 + 2839768 * 2 ^ 59
def prefixEnd_2839768 : Nat := 4983230072969 + 3 ^ 40 * 2839768 * 2
def baseEnd_2839768 : Nat := 486055310419050209446717

theorem tailTrace_2839768 : CollatzResearch.WordTrace tailWord_2839768 prefixEnd_2839768 486055310419050209446717 := by
  unfold tailWord_2839768
  simp only [CollatzResearch.WordTrace]
  refine ⟨51787423988006502303591979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69049898650675336404789305 51787423988006502303591979)
  ·
    refine ⟨77681135982009753455387969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51787423988006502303591979 77681135982009753455387969)
    ·
      refine ⟨58260851986507315091540977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77681135982009753455387969 58260851986507315091540977)
      ·
        refine ⟨43695638989880486318655733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58260851986507315091540977 43695638989880486318655733)
        ·
          refine ⟨4096466155301295592373975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43695638989880486318655733 4096466155301295592373975)
          ·
            refine ⟨6144699232951943388560963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4096466155301295592373975 6144699232951943388560963)
            ·
              refine ⟨9217048849427915082841445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6144699232951943388560963 9217048849427915082841445)
              ·
                refine ⟨1728196659267734078032771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9217048849427915082841445 1728196659267734078032771)
                ·
                  refine ⟨2592294988901601117049157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1728196659267734078032771 2592294988901601117049157)
                  ·
                    refine ⟨486055310419050209446717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2592294988901601117049157 486055310419050209446717)
                    ·
                      rfl

theorem cell23_2839768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_2839768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839768 prefixEnd_2839768 := by exact prefixLift 2839768
  have htrace : WordTrace (prefixWord ++ tailWord_2839768) baseStart_2839768 baseEnd_2839768 := by
    simpa [prefixWord, tailWord_2839768, baseEnd_2839768] using wordTrace_append hprefix tailTrace_2839768
  have hstable : (prefixWord ++ tailWord_2839768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839768).length < 2 ^ (prefixWord ++ tailWord_2839768).sum := by decide
  have hdescent : baseEnd_2839768 < baseStart_2839768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839811 : List Nat := [1, 1, 1, 3, 2, 4, 4, 1, 1, 5]
def baseStart_2839811 : Nat := 118140960795 + 2839811 * 2 ^ 59
def prefixEnd_2839811 : Nat := 4983230072969 + 3 ^ 40 * 2839811 * 2
def baseEnd_2839811 : Nat := 486062670308431320034151

theorem tailTrace_2839811 : CollatzResearch.WordTrace tailWord_2839811 prefixEnd_2839811 486062670308431320034151 := by
  unfold tailWord_2839811
  simp only [CollatzResearch.WordTrace]
  refine ⟨103576416314857222950999287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69050944209904815300666191 103576416314857222950999287)
  ·
    refine ⟨155364624472285834426498931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103576416314857222950999287 155364624472285834426498931)
    ·
      refine ⟨233046936708428751639748397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155364624472285834426498931 233046936708428751639748397)
      ·
        refine ⟨87392601265660781864905649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233046936708428751639748397 87392601265660781864905649)
        ·
          refine ⟨65544450949245586398679237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87392601265660781864905649 65544450949245586398679237)
          ·
            refine ⟨12289584552983547449752357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65544450949245586398679237 12289584552983547449752357)
            ·
              refine ⟨2304297103684415146828567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12289584552983547449752357 2304297103684415146828567)
              ·
                refine ⟨3456445655526622720242851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304297103684415146828567 3456445655526622720242851)
                ·
                  refine ⟨5184668483289934080364277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456445655526622720242851 5184668483289934080364277)
                  ·
                    refine ⟨486062670308431320034151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5184668483289934080364277 486062670308431320034151)
                    ·
                      rfl

theorem cell23_2839811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 1, 5].length) (baseStart_2839811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839811 prefixEnd_2839811 := by exact prefixLift 2839811
  have htrace : WordTrace (prefixWord ++ tailWord_2839811) baseStart_2839811 baseEnd_2839811 := by
    simpa [prefixWord, tailWord_2839811, baseEnd_2839811] using wordTrace_append hprefix tailTrace_2839811
  have hstable : (prefixWord ++ tailWord_2839811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839811).length < 2 ^ (prefixWord ++ tailWord_2839811).sum := by decide
  have hdescent : baseEnd_2839811 < baseStart_2839811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839827 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 4]
def baseStart_2839827 : Nat := 118140960795 + 2839827 * 2 ^ 59
def prefixEnd_2839827 : Nat := 4983230072969 + 3 ^ 40 * 2839827 * 2
def baseEnd_2839827 : Nat := 1458196226615765897502379

theorem tailTrace_2839827 : CollatzResearch.WordTrace tailWord_2839827 prefixEnd_2839827 1458196226615765897502379 := by
  unfold tailWord_2839827
  simp only [CollatzResearch.WordTrace]
  refine ⟨103576999882799257683581735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69051333255199505122387823 103576999882799257683581735)
  ·
    refine ⟨155365499824198886525372603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103576999882799257683581735 155365499824198886525372603)
    ·
      refine ⟨233048249736298329788058905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155365499824198886525372603 233048249736298329788058905)
      ·
        refine ⟨174786187302223747341044179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233048249736298329788058905 174786187302223747341044179)
        ·
          refine ⟨262179280953335621011566269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174786187302223747341044179 262179280953335621011566269)
          ·
            refine ⟨98317230357500857879337351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262179280953335621011566269 98317230357500857879337351)
            ·
              refine ⟨147475845536251286819006027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98317230357500857879337351 147475845536251286819006027)
              ·
                refine ⟨221213768304376930228509041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147475845536251286819006027 221213768304376930228509041)
                ·
                  refine ⟨165910326228282697671381781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221213768304376930228509041 165910326228282697671381781)
                  ·
                    refine ⟨7777046541950751453346021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 165910326228282697671381781 7777046541950751453346021)
                    ·
                      refine ⟨1458196226615765897502379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7777046541950751453346021 1458196226615765897502379)
                      ·
                        rfl

theorem cell23_2839827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_2839827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839827 prefixEnd_2839827 := by exact prefixLift 2839827
  have htrace : WordTrace (prefixWord ++ tailWord_2839827) baseStart_2839827 baseEnd_2839827 := by
    simpa [prefixWord, tailWord_2839827, baseEnd_2839827] using wordTrace_append hprefix tailTrace_2839827
  have hstable : (prefixWord ++ tailWord_2839827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839827).length < 2 ^ (prefixWord ++ tailWord_2839827).sum := by decide
  have hdescent : baseEnd_2839827 < baseStart_2839827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839834 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_2839834 : Nat := 118140960795 + 2839834 * 2 ^ 59
def prefixEnd_2839834 : Nat := 4983230072969 + 3 ^ 40 * 2839834 * 2
def baseEnd_2839834 : Nat := 1458199820980347370114847

theorem tailTrace_2839834 : CollatzResearch.WordTrace tailWord_2839834 prefixEnd_2839834 1458199820980347370114847 := by
  unfold tailWord_2839834
  simp only [CollatzResearch.WordTrace]
  refine ⟨25894313798443474469771639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69051503462515931919391037 25894313798443474469771639)
  ·
    refine ⟨38841470697665211704657459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25894313798443474469771639 38841470697665211704657459)
    ·
      refine ⟨58262206046497817556986189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38841470697665211704657459 58262206046497817556986189)
      ·
        refine ⟨21848327267436681583869821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58262206046497817556986189 21848327267436681583869821)
        ·
          refine ⟨8193122725288755593951183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21848327267436681583869821 8193122725288755593951183)
          ·
            refine ⟨12289684087933133390926775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8193122725288755593951183 12289684087933133390926775)
            ·
              refine ⟨18434526131899700086390163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12289684087933133390926775 18434526131899700086390163)
              ·
                refine ⟨27651789197849550129585245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18434526131899700086390163 27651789197849550129585245)
                ·
                  refine ⟨10369420949193581298594467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27651789197849550129585245 10369420949193581298594467)
                  ·
                    refine ⟨15554131423790371947891701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10369420949193581298594467 15554131423790371947891701)
                    ·
                      refine ⟨1458199820980347370114847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15554131423790371947891701 1458199820980347370114847)
                      ·
                        rfl

theorem cell23_2839834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_2839834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839834 prefixEnd_2839834 := by exact prefixLift 2839834
  have htrace : WordTrace (prefixWord ++ tailWord_2839834) baseStart_2839834 baseEnd_2839834 := by
    simpa [prefixWord, tailWord_2839834, baseEnd_2839834] using wordTrace_append hprefix tailTrace_2839834
  have hstable : (prefixWord ++ tailWord_2839834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839834).length < 2 ^ (prefixWord ++ tailWord_2839834).sum := by decide
  have hdescent : baseEnd_2839834 < baseStart_2839834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839844 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2839844 : Nat := 118140960795 + 2839844 * 2 ^ 59
def prefixEnd_2839844 : Nat := 4983230072969 + 3 ^ 40 * 2839844 * 2
def baseEnd_2839844 : Nat := 1458204955786892330989801

theorem tailTrace_2839844 : CollatzResearch.WordTrace tailWord_2839844 prefixEnd_2839844 1458204955786892330989801 := by
  unfold tailWord_2839844
  simp only [CollatzResearch.WordTrace]
  refine ⟨51788809961868834793475293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69051746615825113057967057 51788809961868834793475293)
  ·
    refine ⟨19420803735700813047553235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51788809961868834793475293 19420803735700813047553235)
    ·
      refine ⟨29131205603551219571329853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19420803735700813047553235 29131205603551219571329853)
      ·
        refine ⟨10924202101331707339248695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29131205603551219571329853 10924202101331707339248695)
        ·
          refine ⟨16386303151997561008873043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10924202101331707339248695 16386303151997561008873043)
          ·
            refine ⟨24579454727996341513309565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16386303151997561008873043 24579454727996341513309565)
            ·
              refine ⟨9217295522998628067491087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24579454727996341513309565 9217295522998628067491087)
              ·
                refine ⟨13825943284497942101236631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9217295522998628067491087 13825943284497942101236631)
                ·
                  refine ⟨20738914926746913151854947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13825943284497942101236631 20738914926746913151854947)
                  ·
                    refine ⟨31108372390120369727782421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20738914926746913151854947 31108372390120369727782421)
                    ·
                      refine ⟨1458204955786892330989801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31108372390120369727782421 1458204955786892330989801)
                      ·
                        rfl

theorem cell23_2839844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2839844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839844 prefixEnd_2839844 := by exact prefixLift 2839844
  have htrace : WordTrace (prefixWord ++ tailWord_2839844) baseStart_2839844 baseEnd_2839844 := by
    simpa [prefixWord, tailWord_2839844, baseEnd_2839844] using wordTrace_append hprefix tailTrace_2839844
  have hstable : (prefixWord ++ tailWord_2839844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839844).length < 2 ^ (prefixWord ++ tailWord_2839844).sum := by decide
  have hdescent : baseEnd_2839844 < baseStart_2839844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839848 : List Nat := [2, 1, 5, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_2839848 : Nat := 118140960795 + 2839848 * 2 ^ 59
def prefixEnd_2839848 : Nat := 4983230072969 + 3 ^ 40 * 2839848 * 2
def baseEnd_2839848 : Nat := 1458207009709510315339783

theorem tailTrace_2839848 : CollatzResearch.WordTrace tailWord_2839848 prefixEnd_2839848 1458207009709510315339783 := by
  unfold tailWord_2839848
  simp only [CollatzResearch.WordTrace]
  refine ⟨51788882907861589135048099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69051843877148785513397465 51788882907861589135048099)
  ·
    refine ⟨77683324361792383702572149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51788882907861589135048099 77683324361792383702572149)
    ·
      refine ⟨7282811658918035972116139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77683324361792383702572149 7282811658918035972116139)
      ·
        refine ⟨10924217488377053958174209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7282811658918035972116139 10924217488377053958174209)
        ·
          refine ⟨8193163116282790468630657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10924217488377053958174209 8193163116282790468630657)
          ·
            refine ⟨6144872337212092851472993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8193163116282790468630657 6144872337212092851472993)
            ·
              refine ⟨4608654252909069638604745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6144872337212092851472993 4608654252909069638604745)
              ·
                refine ⟨3456490689681802228953559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4608654252909069638604745 3456490689681802228953559)
                ·
                  refine ⟨5184736034522703343430339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456490689681802228953559 5184736034522703343430339)
                  ·
                    refine ⟨7777104051784055015145509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5184736034522703343430339 7777104051784055015145509)
                    ·
                      refine ⟨1458207009709510315339783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7777104051784055015145509 1458207009709510315339783)
                      ·
                        rfl

theorem cell23_2839848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_2839848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839848 prefixEnd_2839848 := by exact prefixLift 2839848
  have htrace : WordTrace (prefixWord ++ tailWord_2839848) baseStart_2839848 baseEnd_2839848 := by
    simpa [prefixWord, tailWord_2839848, baseEnd_2839848] using wordTrace_append hprefix tailTrace_2839848
  have hstable : (prefixWord ++ tailWord_2839848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839848).length < 2 ^ (prefixWord ++ tailWord_2839848).sum := by decide
  have hdescent : baseEnd_2839848 < baseStart_2839848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839864 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 3, 3, 3]
def baseStart_2839864 : Nat := 118140960795 + 2839864 * 2 ^ 59
def prefixEnd_2839864 : Nat := 4983230072969 + 3 ^ 40 * 2839864 * 2
def baseEnd_2839864 : Nat := 1458215225399982252739709

theorem tailTrace_2839864 : CollatzResearch.WordTrace tailWord_2839864 prefixEnd_2839864 1458215225399982252739709 := by
  unfold tailWord_2839864
  simp only [CollatzResearch.WordTrace]
  refine ⟨51789174691832606501339323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69052232922443475335119097 51789174691832606501339323)
  ·
    refine ⟨77683762037748909752008985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51789174691832606501339323 77683762037748909752008985)
    ·
      refine ⟨58262821528311682314006739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77683762037748909752008985 58262821528311682314006739)
      ·
        refine ⟨87394232292467523471010109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58262821528311682314006739 87394232292467523471010109)
        ·
          refine ⟨32772837109675321301628791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87394232292467523471010109 32772837109675321301628791)
          ·
            refine ⟨49159255664512981952443187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32772837109675321301628791 49159255664512981952443187)
            ·
              refine ⟨73738883496769472928664781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49159255664512981952443187 73738883496769472928664781)
              ·
                refine ⟨27652081311288552348249293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73738883496769472928664781 27652081311288552348249293)
                ·
                  refine ⟨10369530491733207130593485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27652081311288552348249293 10369530491733207130593485)
                  ·
                    refine ⟨3888573934399952673972557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10369530491733207130593485 3888573934399952673972557)
                    ·
                      refine ⟨1458215225399982252739709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3888573934399952673972557 1458215225399982252739709)
                      ·
                        rfl

theorem cell23_2839864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_2839864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839864 prefixEnd_2839864 := by exact prefixLift 2839864
  have htrace : WordTrace (prefixWord ++ tailWord_2839864) baseStart_2839864 baseEnd_2839864 := by
    simpa [prefixWord, tailWord_2839864, baseEnd_2839864] using wordTrace_append hprefix tailTrace_2839864
  have hstable : (prefixWord ++ tailWord_2839864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839864).length < 2 ^ (prefixWord ++ tailWord_2839864).sum := by decide
  have hdescent : baseEnd_2839864 < baseStart_2839864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839881 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 4, 1, 3]
def baseStart_2839881 : Nat := 118140960795 + 2839881 * 2 ^ 59
def prefixEnd_2839881 : Nat := 4983230072969 + 3 ^ 40 * 2839881 * 2
def baseEnd_2839881 : Nat := 1458223954571108686227131

theorem tailTrace_2839881 : CollatzResearch.WordTrace tailWord_2839881 prefixEnd_2839881 1458223954571108686227131 := by
  unfold tailWord_2839881
  simp only [CollatzResearch.WordTrace]
  refine ⟨103578969424603624906047497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69052646283069083270698331 103578969424603624906047497)
  ·
    refine ⟨77684227068452718679535623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103578969424603624906047497 77684227068452718679535623)
    ·
      refine ⟨116526340602679078019303435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77684227068452718679535623 116526340602679078019303435)
      ·
        refine ⟨174789510904018617028955153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116526340602679078019303435 174789510904018617028955153)
        ·
          refine ⟨131092133178013962771716365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174789510904018617028955153 131092133178013962771716365)
          ·
            refine ⟨49159549941755236039393637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131092133178013962771716365 49159549941755236039393637)
            ·
              refine ⟨9217415614079106757386307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49159549941755236039393637 9217415614079106757386307)
              ·
                refine ⟨13826123421118660136079461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9217415614079106757386307 13826123421118660136079461)
                ·
                  refine ⟨2592398141459748775514899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13826123421118660136079461 2592398141459748775514899)
                  ·
                    refine ⟨3888597212189623163272349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2592398141459748775514899 3888597212189623163272349)
                    ·
                      refine ⟨1458223954571108686227131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3888597212189623163272349 1458223954571108686227131)
                      ·
                        rfl

theorem cell23_2839881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 1, 3].length) (baseStart_2839881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839881 prefixEnd_2839881 := by exact prefixLift 2839881
  have htrace : WordTrace (prefixWord ++ tailWord_2839881) baseStart_2839881 baseEnd_2839881 := by
    simpa [prefixWord, tailWord_2839881, baseEnd_2839881] using wordTrace_append hprefix tailTrace_2839881
  have hstable : (prefixWord ++ tailWord_2839881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839881).length < 2 ^ (prefixWord ++ tailWord_2839881).sum := by decide
  have hdescent : baseEnd_2839881 < baseStart_2839881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839887 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 10]
def baseStart_2839887 : Nat := 118140960795 + 2839887 * 2 ^ 59
def prefixEnd_2839887 : Nat := 4983230072969 + 3 ^ 40 * 2839887 * 2
def baseEnd_2839887 : Nat := 1458227035455035662752103

theorem tailTrace_2839887 : CollatzResearch.WordTrace tailWord_2839887 prefixEnd_2839887 1458227035455035662752103 := by
  unfold tailWord_2839887
  simp only [CollatzResearch.WordTrace]
  refine ⟨103579188262581887930765915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69052792175054591953843943 103579188262581887930765915)
  ·
    refine ⟨155368782393872831896148873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103579188262581887930765915 155368782393872831896148873)
    ·
      refine ⟨116526586795404623922111655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155368782393872831896148873 116526586795404623922111655)
      ·
        refine ⟨174789880193106935883167483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116526586795404623922111655 174789880193106935883167483)
        ·
          refine ⟨262184820289660403824751225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174789880193106935883167483 262184820289660403824751225)
          ·
            refine ⟨196638615217245302868563419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262184820289660403824751225 196638615217245302868563419)
            ·
              refine ⟨294957922825867954302845129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196638615217245302868563419 294957922825867954302845129)
              ·
                refine ⟨221218442119400965727133847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294957922825867954302845129 221218442119400965727133847)
                ·
                  refine ⟨331827663179101448590700771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221218442119400965727133847 331827663179101448590700771)
                  ·
                    refine ⟨497741494768652172886051157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 331827663179101448590700771 497741494768652172886051157)
                    ·
                      refine ⟨1458227035455035662752103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 497741494768652172886051157 1458227035455035662752103)
                      ·
                        rfl

theorem cell23_2839887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_2839887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839887 prefixEnd_2839887 := by exact prefixLift 2839887
  have htrace : WordTrace (prefixWord ++ tailWord_2839887) baseStart_2839887 baseEnd_2839887 := by
    simpa [prefixWord, tailWord_2839887, baseEnd_2839887] using wordTrace_append hprefix tailTrace_2839887
  have hstable : (prefixWord ++ tailWord_2839887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839887).length < 2 ^ (prefixWord ++ tailWord_2839887).sum := by decide
  have hdescent : baseEnd_2839887 < baseStart_2839887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839891 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 3, 3, 2]
def baseStart_2839891 : Nat := 118140960795 + 2839891 * 2 ^ 59
def prefixEnd_2839891 : Nat := 4983230072969 + 3 ^ 40 * 2839891 * 2
def baseEnd_2839891 : Nat := 1458229089377653647102085

theorem tailTrace_2839891 : CollatzResearch.WordTrace tailWord_2839891 prefixEnd_2839891 1458229089377653647102085 := by
  unfold tailWord_2839891
  simp only [CollatzResearch.WordTrace]
  refine ⟨103579334154567396613911527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69052889436378264409274351 103579334154567396613911527)
  ·
    refine ⟨155369001231851094920867291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103579334154567396613911527 155369001231851094920867291)
    ·
      refine ⟨233053501847776642381300937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155369001231851094920867291 233053501847776642381300937)
      ·
        refine ⟨174790126385832481785975703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233053501847776642381300937 174790126385832481785975703)
        ·
          refine ⟨262185189578748722678963555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174790126385832481785975703 262185189578748722678963555)
          ·
            refine ⟨393277784368123084018445333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262185189578748722678963555 393277784368123084018445333)
            ·
              refine ⟨18434896142255769563364625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 393277784368123084018445333 18434896142255769563364625)
              ·
                refine ⟨13826172106691827172523469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18434896142255769563364625 13826172106691827172523469)
                ·
                  refine ⟨5184814540009435189696301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13826172106691827172523469 5184814540009435189696301)
                  ·
                    refine ⟨1944305452503538196136113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5184814540009435189696301 1944305452503538196136113)
                    ·
                      refine ⟨1458229089377653647102085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1944305452503538196136113 1458229089377653647102085)
                      ·
                        rfl

theorem cell23_2839891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 3, 2].length) (baseStart_2839891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839891 prefixEnd_2839891 := by exact prefixLift 2839891
  have htrace : WordTrace (prefixWord ++ tailWord_2839891) baseStart_2839891 baseEnd_2839891 := by
    simpa [prefixWord, tailWord_2839891, baseEnd_2839891] using wordTrace_append hprefix tailTrace_2839891
  have hstable : (prefixWord ++ tailWord_2839891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839891).length < 2 ^ (prefixWord ++ tailWord_2839891).sum := by decide
  have hdescent : baseEnd_2839891 < baseStart_2839891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839908 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 3, 3, 2]
def baseStart_2839908 : Nat := 118140960795 + 2839908 * 2 ^ 59
def prefixEnd_2839908 : Nat := 4983230072969 + 3 ^ 40 * 2839908 * 2
def baseEnd_2839908 : Nat := 1458237818548780080589507

theorem tailTrace_2839908 : CollatzResearch.WordTrace tailWord_2839908 prefixEnd_2839908 1458237818548780080589507 := by
  unfold tailWord_2839908
  simp only [CollatzResearch.WordTrace]
  refine ⟨51789977097752904258640189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69053302797003872344853585 51789977097752904258640189)
  ·
    refine ⟨19421241411657339096990071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51789977097752904258640189 19421241411657339096990071)
    ·
      refine ⟨29131862117486008645485107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19421241411657339096990071 29131862117486008645485107)
      ·
        refine ⟨43697793176229012968227661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29131862117486008645485107 43697793176229012968227661)
        ·
          refine ⟨16386672441085879863085373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43697793176229012968227661 16386672441085879863085373)
          ·
            refine ⟨6145002165407204948657015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16386672441085879863085373 6145002165407204948657015)
            ·
              refine ⟨9217503248110807422985523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6145002165407204948657015 9217503248110807422985523)
              ·
                refine ⟨13826254872166211134478285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9217503248110807422985523 13826254872166211134478285)
                ·
                  refine ⟨5184845577062329175429357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13826254872166211134478285 5184845577062329175429357)
                  ·
                    refine ⟨1944317091398373440786009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5184845577062329175429357 1944317091398373440786009)
                    ·
                      refine ⟨1458237818548780080589507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1944317091398373440786009 1458237818548780080589507)
                      ·
                        rfl

theorem cell23_2839908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_2839908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839908 prefixEnd_2839908 := by exact prefixLift 2839908
  have htrace : WordTrace (prefixWord ++ tailWord_2839908) baseStart_2839908 baseEnd_2839908 := by
    simpa [prefixWord, tailWord_2839908, baseEnd_2839908] using wordTrace_append hprefix tailTrace_2839908
  have hstable : (prefixWord ++ tailWord_2839908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839908).length < 2 ^ (prefixWord ++ tailWord_2839908).sum := by decide
  have hdescent : baseEnd_2839908 < baseStart_2839908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839921 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 3, 4, 2]
def baseStart_2839921 : Nat := 118140960795 + 2839921 * 2 ^ 59
def prefixEnd_2839921 : Nat := 4983230072969 + 3 ^ 40 * 2839921 * 2
def baseEnd_2839921 : Nat := 1458244493797288529726947

theorem tailTrace_2839921 : CollatzResearch.WordTrace tailWord_2839921 prefixEnd_2839921 1458244493797288529726947 := by
  unfold tailWord_2839921
  simp only [CollatzResearch.WordTrace]
  refine ⟨103580428344458711737503617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69053618896305807825002411 103580428344458711737503617)
  ·
    refine ⟨77685321258344033803127713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103580428344458711737503617 77685321258344033803127713)
    ·
      refine ⟨58263990943758025352345785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77685321258344033803127713 58263990943758025352345785)
      ·
        refine ⟨43697993207818519014259339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58263990943758025352345785 43697993207818519014259339)
        ·
          refine ⟨65546989811727778521389009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43697993207818519014259339 65546989811727778521389009)
          ·
            refine ⟨49160242358795833891041757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65546989811727778521389009 49160242358795833891041757)
            ·
              refine ⟨18435090884548437709140659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49160242358795833891041757 18435090884548437709140659)
              ·
                refine ⟨27652636326822656563710989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18435090884548437709140659 27652636326822656563710989)
                ·
                  refine ⟨10369738622558496211391621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27652636326822656563710989 10369738622558496211391621)
                  ·
                    refine ⟨1944325991729718039635929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10369738622558496211391621 1944325991729718039635929)
                    ·
                      refine ⟨1458244493797288529726947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1944325991729718039635929 1458244493797288529726947)
                      ·
                        rfl

theorem cell23_2839921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_2839921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839921 prefixEnd_2839921 := by exact prefixLift 2839921
  have htrace : WordTrace (prefixWord ++ tailWord_2839921) baseStart_2839921 baseEnd_2839921 := by
    simpa [prefixWord, tailWord_2839921, baseEnd_2839921] using wordTrace_append hprefix tailTrace_2839921
  have hstable : (prefixWord ++ tailWord_2839921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839921).length < 2 ^ (prefixWord ++ tailWord_2839921).sum := by decide
  have hdescent : baseEnd_2839921 < baseStart_2839921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839938 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2839938 : Nat := 118140960795 + 2839938 * 2 ^ 59
def prefixEnd_2839938 : Nat := 4983230072969 + 3 ^ 40 * 2839938 * 2
def baseEnd_2839938 : Nat := 1458253222968414963214369

theorem tailTrace_2839938 : CollatzResearch.WordTrace tailWord_2839938 prefixEnd_2839938 1458253222968414963214369 := by
  unfold tailWord_2839938
  simp only [CollatzResearch.WordTrace]
  refine ⟨25895262096349280910218117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69054032256931415760581645 25895262096349280910218117)
  ·
    refine ⟨4855361643065490170665897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25895262096349280910218117 4855361643065490170665897)
    ·
      refine ⟨3641521232299117627999423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4855361643065490170665897 3641521232299117627999423)
      ·
        refine ⟨5462281848448676441999135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3641521232299117627999423 5462281848448676441999135)
        ·
          refine ⟨8193422772673014662998703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5462281848448676441999135 8193422772673014662998703)
          ·
            refine ⟨12290134159009521994498055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8193422772673014662998703 12290134159009521994498055)
            ·
              refine ⟨18435201238514282991747083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12290134159009521994498055 18435201238514282991747083)
              ·
                refine ⟨27652801857771424487620625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18435201238514282991747083 27652801857771424487620625)
                ·
                  refine ⟨20739601393328568365715469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27652801857771424487620625 20739601393328568365715469)
                  ·
                    refine ⟨7777350522498213137143301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20739601393328568365715469 7777350522498213137143301)
                    ·
                      refine ⟨1458253222968414963214369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7777350522498213137143301 1458253222968414963214369)
                      ·
                        rfl

theorem cell23_2839938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2839938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839938 prefixEnd_2839938 := by exact prefixLift 2839938
  have htrace : WordTrace (prefixWord ++ tailWord_2839938) baseStart_2839938 baseEnd_2839938 := by
    simpa [prefixWord, tailWord_2839938, baseEnd_2839938] using wordTrace_append hprefix tailTrace_2839938
  have hstable : (prefixWord ++ tailWord_2839938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839938).length < 2 ^ (prefixWord ++ tailWord_2839938).sum := by decide
  have hdescent : baseEnd_2839938 < baseStart_2839938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839976 : List Nat := [2, 1, 6, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_2839976 : Nat := 118140960795 + 2839976 * 2 ^ 59
def prefixEnd_2839976 : Nat := 4983230072969 + 3 ^ 40 * 2839976 * 2
def baseEnd_2839976 : Nat := 1458272735233285814539195

theorem tailTrace_2839976 : CollatzResearch.WordTrace tailWord_2839976 prefixEnd_2839976 1458272735233285814539195 := by
  unfold tailWord_2839976
  simp only [CollatzResearch.WordTrace]
  refine ⟨51791217179629728065377891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69054956239506304087170521 51791217179629728065377891)
  ·
    refine ⟨77686825769444592098066837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51791217179629728065377891 77686825769444592098066837)
    ·
      refine ⟨3641569957942715254596883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77686825769444592098066837 3641569957942715254596883)
      ·
        refine ⟨5462354936914072881895325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3641569957942715254596883 5462354936914072881895325)
        ·
          refine ⟨2048383101342777330710747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5462354936914072881895325 2048383101342777330710747)
          ·
            refine ⟨3072574652014165996066121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048383101342777330710747 3072574652014165996066121)
            ·
              refine ⟨2304430989010624497049591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3072574652014165996066121 2304430989010624497049591)
              ·
                refine ⟨3456646483515936745574387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304430989010624497049591 3456646483515936745574387)
                ·
                  refine ⟨5184969725273905118361581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456646483515936745574387 5184969725273905118361581)
                  ·
                    refine ⟨1944363646977714419385593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5184969725273905118361581 1944363646977714419385593)
                    ·
                      refine ⟨1458272735233285814539195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1944363646977714419385593 1458272735233285814539195)
                      ·
                        rfl

theorem cell23_2839976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_2839976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839976 prefixEnd_2839976 := by exact prefixLift 2839976
  have htrace : WordTrace (prefixWord ++ tailWord_2839976) baseStart_2839976 baseEnd_2839976 := by
    simpa [prefixWord, tailWord_2839976, baseEnd_2839976] using wordTrace_append hprefix tailTrace_2839976
  have hstable : (prefixWord ++ tailWord_2839976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839976).length < 2 ^ (prefixWord ++ tailWord_2839976).sum := by decide
  have hdescent : baseEnd_2839976 < baseStart_2839976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2839984 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 5]
def baseStart_2839984 : Nat := 118140960795 + 2839984 * 2 ^ 59
def prefixEnd_2839984 : Nat := 4983230072969 + 3 ^ 40 * 2839984 * 2
def baseEnd_2839984 : Nat := 1458276843078521783239157

theorem tailTrace_2839984 : CollatzResearch.WordTrace tailWord_2839984 prefixEnd_2839984 1458276843078521783239157 := by
  unfold tailWord_2839984
  simp only [CollatzResearch.WordTrace]
  refine ⟨51791363071615236748523503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69055150762153648998031337 51791363071615236748523503)
  ·
    refine ⟨77687044607422855122785255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51791363071615236748523503 77687044607422855122785255)
    ·
      refine ⟨116530566911134282684177883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77687044607422855122785255 116530566911134282684177883)
      ·
        refine ⟨174795850366701424026266825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116530566911134282684177883 174795850366701424026266825)
        ·
          refine ⟨131096887775026068019700119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174795850366701424026266825 131096887775026068019700119)
          ·
            refine ⟨196645331662539102029550179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131096887775026068019700119 196645331662539102029550179)
            ·
              refine ⟨294967997493808653044325269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196645331662539102029550179 294967997493808653044325269)
              ·
                refine ⟨13826624882522280611452747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 294967997493808653044325269 13826624882522280611452747)
                ·
                  refine ⟨20739937323783420917179121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13826624882522280611452747 20739937323783420917179121)
                  ·
                    refine ⟨15554952992837565687884341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20739937323783420917179121 15554952992837565687884341)
                    ·
                      refine ⟨1458276843078521783239157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15554952992837565687884341 1458276843078521783239157)
                      ·
                        rfl

theorem cell23_2839984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_2839984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2839984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2839984 prefixEnd_2839984 := by exact prefixLift 2839984
  have htrace : WordTrace (prefixWord ++ tailWord_2839984) baseStart_2839984 baseEnd_2839984 := by
    simpa [prefixWord, tailWord_2839984, baseEnd_2839984] using wordTrace_append hprefix tailTrace_2839984
  have hstable : (prefixWord ++ tailWord_2839984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2839984).length < 2 ^ (prefixWord ++ tailWord_2839984).sum := by decide
  have hdescent : baseEnd_2839984 < baseStart_2839984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2839984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840031 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 3]
def baseStart_2840031 : Nat := 118140960795 + 2840031 * 2 ^ 59
def prefixEnd_2840031 : Nat := 4983230072969 + 3 ^ 40 * 2840031 * 2
def baseEnd_2840031 : Nat := 1458300976669283099351441

theorem tailTrace_2840031 : CollatzResearch.WordTrace tailWord_2840031 prefixEnd_2840031 1458300976669283099351441 := by
  unfold tailWord_2840031
  simp only [CollatzResearch.WordTrace]
  refine ⟨103584440374060200524007947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69056293582706800349338631 103584440374060200524007947)
  ·
    refine ⟨155376660561090300786011921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103584440374060200524007947 155376660561090300786011921)
    ·
      refine ⟨116532495420817725589508941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155376660561090300786011921 116532495420817725589508941)
      ·
        refine ⟨43699685782806647096065853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116532495420817725589508941 43699685782806647096065853)
        ·
          refine ⟨16387382168552492661024695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43699685782806647096065853 16387382168552492661024695)
          ·
            refine ⟨24581073252828738991537043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16387382168552492661024695 24581073252828738991537043)
            ·
              refine ⟨36871609879243108487305565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24581073252828738991537043 36871609879243108487305565)
              ·
                refine ⟨13826853704716165682739587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36871609879243108487305565 13826853704716165682739587)
                ·
                  refine ⟨20740280557074248524109381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13826853704716165682739587 20740280557074248524109381)
                  ·
                    refine ⟨3888802604451421598270509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20740280557074248524109381 3888802604451421598270509)
                    ·
                      refine ⟨1458300976669283099351441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3888802604451421598270509 1458300976669283099351441)
                      ·
                        rfl

theorem cell23_2840031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_2840031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840031 prefixEnd_2840031 := by exact prefixLift 2840031
  have htrace : WordTrace (prefixWord ++ tailWord_2840031) baseStart_2840031 baseEnd_2840031 := by
    simpa [prefixWord, tailWord_2840031, baseEnd_2840031] using wordTrace_append hprefix tailTrace_2840031
  have hstable : (prefixWord ++ tailWord_2840031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840031).length < 2 ^ (prefixWord ++ tailWord_2840031).sum := by decide
  have hdescent : baseEnd_2840031 < baseStart_2840031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840045 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2840045 : Nat := 118140960795 + 2840045 * 2 ^ 59
def prefixEnd_2840045 : Nat := 4983230072969 + 3 ^ 40 * 2840045 * 2
def baseEnd_2840045 : Nat := 1458308165398446044576377

theorem tailTrace_2840045 : CollatzResearch.WordTrace tailWord_2840045 prefixEnd_2840045 1458308165398446044576377 := by
  unfold tailWord_2840045
  simp only [CollatzResearch.WordTrace]
  refine ⟨103584950996009480915017589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69056633997339653943345059 103584950996009480915017589)
  ·
    refine ⟨9711089155875888835782899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103584950996009480915017589 9711089155875888835782899)
    ·
      refine ⟨14566633733813833253674349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9711089155875888835782899 14566633733813833253674349)
      ·
        refine ⟨5462487650180187470127881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14566633733813833253674349 5462487650180187470127881)
        ·
          refine ⟨4096865737635140602595911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5462487650180187470127881 4096865737635140602595911)
          ·
            refine ⟨6145298606452710903893867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4096865737635140602595911 6145298606452710903893867)
            ·
              refine ⟨9217947909679066355840801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6145298606452710903893867 9217947909679066355840801)
              ·
                refine ⟨6913460932259299766880601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9217947909679066355840801 6913460932259299766880601)
                ·
                  refine ⟨5185095699194474825160451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6913460932259299766880601 5185095699194474825160451)
                  ·
                    refine ⟨7777643548791712237740677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5185095699194474825160451 7777643548791712237740677)
                    ·
                      refine ⟨1458308165398446044576377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7777643548791712237740677 1458308165398446044576377)
                      ·
                        rfl

theorem cell23_2840045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2840045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840045 prefixEnd_2840045 := by exact prefixLift 2840045
  have htrace : WordTrace (prefixWord ++ tailWord_2840045) baseStart_2840045 baseEnd_2840045 := by
    simpa [prefixWord, tailWord_2840045, baseEnd_2840045] using wordTrace_append hprefix tailTrace_2840045
  have hstable : (prefixWord ++ tailWord_2840045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840045).length < 2 ^ (prefixWord ++ tailWord_2840045).sum := by decide
  have hdescent : baseEnd_2840045 < baseStart_2840045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840048 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 3]
def baseStart_2840048 : Nat := 118140960795 + 2840048 * 2 ^ 59
def prefixEnd_2840048 : Nat := 4983230072969 + 3 ^ 40 * 2840048 * 2
def baseEnd_2840048 : Nat := 1458309705840409532838863

theorem tailTrace_2840048 : CollatzResearch.WordTrace tailWord_2840048 prefixEnd_2840048 1458309705840409532838863 := by
  unfold tailWord_2840048
  simp only [CollatzResearch.WordTrace]
  refine ⟨51792530207499306213688399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69056706943332408284917865 51792530207499306213688399)
  ·
    refine ⟨77688795311248959320532599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51792530207499306213688399 77688795311248959320532599)
    ·
      refine ⟨116533192966873438980798899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77688795311248959320532599 116533192966873438980798899)
      ·
        refine ⟨174799789450310158471198349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116533192966873438980798899 174799789450310158471198349)
        ·
          refine ⟨65549921043866309426699381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174799789450310158471198349 65549921043866309426699381)
          ·
            refine ⟨6145305097862466508753067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65549921043866309426699381 6145305097862466508753067)
            ·
              refine ⟨9217957646793699763129601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6145305097862466508753067 9217957646793699763129601)
              ·
                refine ⟨6913468235095274822347201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9217957646793699763129601 6913468235095274822347201)
                ·
                  refine ⟨5185101176321456116760401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6913468235095274822347201 5185101176321456116760401)
                  ·
                    refine ⟨3888825882241092087570301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5185101176321456116760401 3888825882241092087570301)
                    ·
                      refine ⟨1458309705840409532838863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3888825882241092087570301 1458309705840409532838863)
                      ·
                        rfl

theorem cell23_2840048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 3].length) (baseStart_2840048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840048 prefixEnd_2840048 := by exact prefixLift 2840048
  have htrace : WordTrace (prefixWord ++ tailWord_2840048) baseStart_2840048 baseEnd_2840048 := by
    simpa [prefixWord, tailWord_2840048, baseEnd_2840048] using wordTrace_append hprefix tailTrace_2840048
  have hstable : (prefixWord ++ tailWord_2840048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840048).length < 2 ^ (prefixWord ++ tailWord_2840048).sum := by decide
  have hdescent : baseEnd_2840048 < baseStart_2840048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840081 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 3, 5]
def baseStart_2840081 : Nat := 118140960795 + 2840081 * 2 ^ 59
def prefixEnd_2840081 : Nat := 4983230072969 + 3 ^ 40 * 2840081 * 2
def baseEnd_2840081 : Nat := 486108883567335967908737

theorem tailTrace_2840081 : CollatzResearch.WordTrace tailWord_2840081 prefixEnd_2840081 486108883567335967908737 := by
  unfold tailWord_2840081
  simp only [CollatzResearch.WordTrace]
  refine ⟨103586264023879059063328097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69057509349252706042218731 103586264023879059063328097)
  ·
    refine ⟨77689698017909294297496073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103586264023879059063328097 77689698017909294297496073)
    ·
      refine ⟨58267273513431970723122055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77689698017909294297496073 58267273513431970723122055)
      ·
        refine ⟨87400910270147956084683083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58267273513431970723122055 87400910270147956084683083)
        ·
          refine ⟨131101365405221934127024625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87400910270147956084683083 131101365405221934127024625)
          ·
            refine ⟨98326024053916450595268469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131101365405221934127024625 98326024053916450595268469)
            ·
              refine ⟨9218064755054667243306419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98326024053916450595268469 9218064755054667243306419)
              ·
                refine ⟨13827097132582000864959629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9218064755054667243306419 13827097132582000864959629)
                ·
                  refine ⟨5185161424718250324359861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13827097132582000864959629 5185161424718250324359861)
                  ·
                    refine ⟨486108883567335967908737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5185161424718250324359861 486108883567335967908737)
                    ·
                      rfl

theorem cell23_2840081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_2840081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840081 prefixEnd_2840081 := by exact prefixLift 2840081
  have htrace : WordTrace (prefixWord ++ tailWord_2840081) baseStart_2840081 baseEnd_2840081 := by
    simpa [prefixWord, tailWord_2840081, baseEnd_2840081] using wordTrace_append hprefix tailTrace_2840081
  have hstable : (prefixWord ++ tailWord_2840081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840081).length < 2 ^ (prefixWord ++ tailWord_2840081).sum := by decide
  have hdescent : baseEnd_2840081 < baseStart_2840081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840098 : List Nat := [3, 3, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_2840098 : Nat := 118140960795 + 2840098 * 2 ^ 59
def prefixEnd_2840098 : Nat := 4983230072969 + 3 ^ 40 * 2840098 * 2
def baseEnd_2840098 : Nat := 486111793291044779071211

theorem tailTrace_2840098 : CollatzResearch.WordTrace tailWord_2840098 prefixEnd_2840098 486111793291044779071211 := by
  unfold tailWord_2840098
  simp only [CollatzResearch.WordTrace]
  refine ⟨25896721016204367741674237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69057922709878313977797965 25896721016204367741674237)
  ·
    refine ⟨9711270381076637903127839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25896721016204367741674237 9711270381076637903127839)
    ·
      refine ⟨14566905571614956854691759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9711270381076637903127839 14566905571614956854691759)
      ·
        refine ⟨21850358357422435282037639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14566905571614956854691759 21850358357422435282037639)
        ·
          refine ⟨32775537536133652923056459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21850358357422435282037639 32775537536133652923056459)
          ·
            refine ⟨49163306304200479384584689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32775537536133652923056459 49163306304200479384584689)
            ·
              refine ⟨36872479728150359538438517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49163306304200479384584689 36872479728150359538438517)
              ·
                refine ⟨3456794974514096206728611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36872479728150359538438517 3456794974514096206728611)
                ·
                  refine ⟨5185192461771144310092917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456794974514096206728611 5185192461771144310092917)
                  ·
                    refine ⟨486111793291044779071211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5185192461771144310092917 486111793291044779071211)
                    ·
                      rfl

theorem cell23_2840098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_2840098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840098 prefixEnd_2840098 := by exact prefixLift 2840098
  have htrace : WordTrace (prefixWord ++ tailWord_2840098) baseStart_2840098 baseEnd_2840098 := by
    simpa [prefixWord, tailWord_2840098, baseEnd_2840098] using wordTrace_append hprefix tailTrace_2840098
  have hstable : (prefixWord ++ tailWord_2840098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840098).length < 2 ^ (prefixWord ++ tailWord_2840098).sum := by decide
  have hdescent : baseEnd_2840098 < baseStart_2840098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840138 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_2840138 : Nat := 118140960795 + 2840138 * 2 ^ 59
def prefixEnd_2840138 : Nat := 4983230072969 + 3 ^ 40 * 2840138 * 2
def baseEnd_2840138 : Nat := 1458355919099314180713449

theorem tailTrace_2840138 : CollatzResearch.WordTrace tailWord_2840138 prefixEnd_2840138 1458355919099314180713449 := by
  unfold tailWord_2840138
  simp only [CollatzResearch.WordTrace]
  refine ⟨25897085746168139449538267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69058895323115038532102045 25897085746168139449538267)
  ·
    refine ⟨38845628619252209174307401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25897085746168139449538267 38845628619252209174307401)
    ·
      refine ⟨29134221464439156880730551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38845628619252209174307401 29134221464439156880730551)
      ·
        refine ⟨43701332196658735321095827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29134221464439156880730551 43701332196658735321095827)
        ·
          refine ⟨65551998294988102981643741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43701332196658735321095827 65551998294988102981643741)
          ·
            refine ⟨24581999360620538618116403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65551998294988102981643741 24581999360620538618116403)
            ·
              refine ⟨36872999040930807927174605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24581999360620538618116403 36872999040930807927174605)
              ·
                refine ⟨13827374640349052972690477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36872999040930807927174605 13827374640349052972690477)
                ·
                  refine ⟨5185265490130894864758929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13827374640349052972690477 5185265490130894864758929)
                  ·
                    refine ⟨3888949117598171148569197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5185265490130894864758929 3888949117598171148569197)
                    ·
                      refine ⟨1458355919099314180713449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3888949117598171148569197 1458355919099314180713449)
                      ·
                        rfl

theorem cell23_2840138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_2840138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840138 prefixEnd_2840138 := by exact prefixLift 2840138
  have htrace : WordTrace (prefixWord ++ tailWord_2840138) baseStart_2840138 baseEnd_2840138 := by
    simpa [prefixWord, tailWord_2840138, baseEnd_2840138] using wordTrace_append hprefix tailTrace_2840138
  have hstable : (prefixWord ++ tailWord_2840138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840138).length < 2 ^ (prefixWord ++ tailWord_2840138).sum := by decide
  have hdescent : baseEnd_2840138 < baseStart_2840138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840148 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_2840148 : Nat := 118140960795 + 2840148 * 2 ^ 59
def prefixEnd_2840148 : Nat := 4983230072969 + 3 ^ 40 * 2840148 * 2
def baseEnd_2840148 : Nat := 1458361053905859141588403

theorem tailTrace_2840148 : CollatzResearch.WordTrace tailWord_2840148 prefixEnd_2840148 1458361053905859141588403 := by
  unfold tailWord_2840148
  simp only [CollatzResearch.WordTrace]
  refine ⟨51794353857318164753008549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69059138476424219670678065 51794353857318164753008549)
  ·
    refine ⟨9711441348247155891189103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51794353857318164753008549 9711441348247155891189103)
    ·
      refine ⟨14567162022370733836783655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9711441348247155891189103 14567162022370733836783655)
      ·
        refine ⟨21850743033556100755175483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14567162022370733836783655 21850743033556100755175483)
        ·
          refine ⟨32776114550334151132763225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21850743033556100755175483 32776114550334151132763225)
          ·
            refine ⟨24582085912750613349572419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32776114550334151132763225 24582085912750613349572419)
            ·
              refine ⟨36873128869125920024358629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24582085912750613349572419 36873128869125920024358629)
              ·
                refine ⟨6913711662961110004567243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36873128869125920024358629 6913711662961110004567243)
                ·
                  refine ⟨10370567494441665006850865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6913711662961110004567243 10370567494441665006850865)
                  ·
                    refine ⟨7777925620831248755138149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10370567494441665006850865 7777925620831248755138149)
                    ·
                      refine ⟨1458361053905859141588403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7777925620831248755138149 1458361053905859141588403)
                      ·
                        rfl

theorem cell23_2840148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_2840148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840148 prefixEnd_2840148 := by exact prefixLift 2840148
  have htrace : WordTrace (prefixWord ++ tailWord_2840148) baseStart_2840148 baseEnd_2840148 := by
    simpa [prefixWord, tailWord_2840148, baseEnd_2840148] using wordTrace_append hprefix tailTrace_2840148
  have hstable : (prefixWord ++ tailWord_2840148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840148).length < 2 ^ (prefixWord ++ tailWord_2840148).sum := by decide
  have hdescent : baseEnd_2840148 < baseStart_2840148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840182 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2840182 : Nat := 118140960795 + 2840182 * 2 ^ 59
def prefixEnd_2840182 : Nat := 4983230072969 + 3 ^ 40 * 2840182 * 2
def baseEnd_2840182 : Nat := 1458378512248112008563247

theorem tailTrace_2840182 : CollatzResearch.WordTrace tailWord_2840182 prefixEnd_2840182 1458378512248112008563247 := by
  unfold tailWord_2840182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6474371737282072082047175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69059965197675435541836533 6474371737282072082047175)
  ·
    refine ⟨9711557605923108123070763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6474371737282072082047175 9711557605923108123070763)
    ·
      refine ⟨14567336408884662184606145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9711557605923108123070763 14567336408884662184606145)
      ·
        refine ⟨10925502306663496638454609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14567336408884662184606145 10925502306663496638454609)
        ·
          refine ⟨8194126729997622478840957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10925502306663496638454609 8194126729997622478840957)
          ·
            refine ⟨3072797523749108429565359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8194126729997622478840957 3072797523749108429565359)
            ·
              refine ⟨4609196285623662644348039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072797523749108429565359 4609196285623662644348039)
              ·
                refine ⟨6913794428435493966522059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4609196285623662644348039 6913794428435493966522059)
                ·
                  refine ⟨10370691642653240949783089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6913794428435493966522059 10370691642653240949783089)
                  ·
                    refine ⟨7778018731989930712337317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10370691642653240949783089 7778018731989930712337317)
                    ·
                      refine ⟨1458378512248112008563247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7778018731989930712337317 1458378512248112008563247)
                      ·
                        rfl

theorem cell23_2840182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2840182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840182 prefixEnd_2840182 := by exact prefixLift 2840182
  have htrace : WordTrace (prefixWord ++ tailWord_2840182) baseStart_2840182 baseEnd_2840182 := by
    simpa [prefixWord, tailWord_2840182, baseEnd_2840182] using wordTrace_append hprefix tailTrace_2840182
  have hstable : (prefixWord ++ tailWord_2840182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840182).length < 2 ^ (prefixWord ++ tailWord_2840182).sum := by decide
  have hdescent : baseEnd_2840182 < baseStart_2840182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840191 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 4]
def baseStart_2840191 : Nat := 118140960795 + 2840191 * 2 ^ 59
def prefixEnd_2840191 : Nat := 4983230072969 + 3 ^ 40 * 2840191 * 2
def baseEnd_2840191 : Nat := 1458383133574002473350705

theorem tailTrace_2840191 : CollatzResearch.WordTrace tailWord_2840191 prefixEnd_2840191 1458383133574002473350705 := by
  unfold tailWord_2840191
  simp only [CollatzResearch.WordTrace]
  refine ⟨103590276053480547849832427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69060184035653698566554951 103590276053480547849832427)
  ·
    refine ⟨155385414080220821774748641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103590276053480547849832427 155385414080220821774748641)
    ·
      refine ⟨116539060560165616331061481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155385414080220821774748641 116539060560165616331061481)
      ·
        refine ⟨87404295420124212248296111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116539060560165616331061481 87404295420124212248296111)
        ·
          refine ⟨131106443130186318372444167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87404295420124212248296111 131106443130186318372444167)
          ·
            refine ⟨196659664695279477558666251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131106443130186318372444167 196659664695279477558666251)
            ·
              refine ⟨294989497042919216337999377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196659664695279477558666251 294989497042919216337999377)
              ·
                refine ⟨221242122782189412253499533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294989497042919216337999377 221242122782189412253499533)
                ·
                  refine ⟨82965796043321029595062325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221242122782189412253499533 82965796043321029595062325)
                  ·
                    refine ⟨7778043379061346524537093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82965796043321029595062325 7778043379061346524537093)
                    ·
                      refine ⟨1458383133574002473350705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7778043379061346524537093 1458383133574002473350705)
                      ·
                        rfl

theorem cell23_2840191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_2840191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840191 prefixEnd_2840191 := by exact prefixLift 2840191
  have htrace : WordTrace (prefixWord ++ tailWord_2840191) baseStart_2840191 baseEnd_2840191 := by
    simpa [prefixWord, tailWord_2840191, baseEnd_2840191] using wordTrace_append hprefix tailTrace_2840191
  have hstable : (prefixWord ++ tailWord_2840191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840191).length < 2 ^ (prefixWord ++ tailWord_2840191).sum := by decide
  have hdescent : baseEnd_2840191 < baseStart_2840191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840201 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 1, 8]
def baseStart_2840201 : Nat := 118140960795 + 2840201 * 2 ^ 59
def prefixEnd_2840201 : Nat := 4983230072969 + 3 ^ 40 * 2840201 * 2
def baseEnd_2840201 : Nat := 486129422793515811408553

theorem tailTrace_2840201 : CollatzResearch.WordTrace tailWord_2840201 prefixEnd_2840201 486129422793515811408553 := by
  unfold tailWord_2840201
  simp only [CollatzResearch.WordTrace]
  refine ⟨103590640783444319557696457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69060427188962879705130971 103590640783444319557696457)
  ·
    refine ⟨77692980587583239668272343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103590640783444319557696457 77692980587583239668272343)
    ·
      refine ⟨116539470881374859502408515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77692980587583239668272343 116539470881374859502408515)
      ·
        refine ⟨174809206322062289253612773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116539470881374859502408515 174809206322062289253612773)
        ·
          refine ⟨32776726185386679235052395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174809206322062289253612773 32776726185386679235052395)
          ·
            refine ⟨49165089278080018852578593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32776726185386679235052395 49165089278080018852578593)
            ·
              refine ⟨36873816958560014139433945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49165089278080018852578593 36873816958560014139433945)
              ·
                refine ⟨27655362718920010604575459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36873816958560014139433945 27655362718920010604575459)
                ·
                  refine ⟨41483044078380015906863189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27655362718920010604575459 41483044078380015906863189)
                  ·
                    refine ⟨486129422793515811408553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41483044078380015906863189 486129422793515811408553)
                    ·
                      rfl

theorem cell23_2840201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_2840201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840201 prefixEnd_2840201 := by exact prefixLift 2840201
  have htrace : WordTrace (prefixWord ++ tailWord_2840201) baseStart_2840201 baseEnd_2840201 := by
    simpa [prefixWord, tailWord_2840201, baseEnd_2840201] using wordTrace_append hprefix tailTrace_2840201
  have hstable : (prefixWord ++ tailWord_2840201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840201).length < 2 ^ (prefixWord ++ tailWord_2840201).sum := by decide
  have hdescent : baseEnd_2840201 < baseStart_2840201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840246 : List Nat := [5, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_2840246 : Nat := 118140960795 + 2840246 * 2 ^ 59
def prefixEnd_2840246 : Nat := 4983230072969 + 3 ^ 40 * 2840246 * 2
def baseEnd_2840246 : Nat := 1458411375009999758162953

theorem tailTrace_2840246 : CollatzResearch.WordTrace tailWord_2840246 prefixEnd_2840246 1458411375009999758162953 := by
  unfold tailWord_2840246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6474517629267580765192787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69061521378854194828723061 6474517629267580765192787)
  ·
    refine ⟨9711776443901371147789181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6474517629267580765192787 9711776443901371147789181)
    ·
      refine ⟨3641916166463014180420943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9711776443901371147789181 3641916166463014180420943)
      ·
        refine ⟨5462874249694521270631415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3641916166463014180420943 5462874249694521270631415)
        ·
          refine ⟨8194311374541781905947123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5462874249694521270631415 8194311374541781905947123)
          ·
            refine ⟨12291467061812672858920685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8194311374541781905947123 12291467061812672858920685)
            ·
              refine ⟨4609300148179752322095257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12291467061812672858920685 4609300148179752322095257)
              ·
                refine ⟨3456975111134814241571443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4609300148179752322095257 3456975111134814241571443)
                ·
                  refine ⟨5185462666702221362357165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456975111134814241571443 5185462666702221362357165)
                  ·
                    refine ⟨1944548500013333010883937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5185462666702221362357165 1944548500013333010883937)
                    ·
                      refine ⟨1458411375009999758162953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1944548500013333010883937 1458411375009999758162953)
                      ·
                        rfl

theorem cell23_2840246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_2840246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840246 prefixEnd_2840246 := by exact prefixLift 2840246
  have htrace : WordTrace (prefixWord ++ tailWord_2840246) baseStart_2840246 baseEnd_2840246 := by
    simpa [prefixWord, tailWord_2840246, baseEnd_2840246] using wordTrace_append hprefix tailTrace_2840246
  have hstable : (prefixWord ++ tailWord_2840246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840246).length < 2 ^ (prefixWord ++ tailWord_2840246).sum := by decide
  have hdescent : baseEnd_2840246 < baseStart_2840246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840251 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 8]
def baseStart_2840251 : Nat := 118140960795 + 2840251 * 2 ^ 59
def prefixEnd_2840251 : Nat := 4983230072969 + 3 ^ 40 * 2840251 * 2
def baseEnd_2840251 : Nat := 1458413942413272238600429

theorem tailTrace_2840251 : CollatzResearch.WordTrace tailWord_2840251 prefixEnd_2840251 1458413942413272238600429 := by
  unfold tailWord_2840251
  simp only [CollatzResearch.WordTrace]
  refine ⟨103592464433263178097016607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69061642955508785398011071 103592464433263178097016607)
  ·
    refine ⟨155388696649894767145524911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103592464433263178097016607 155388696649894767145524911)
    ·
      refine ⟨233083044974842150718287367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155388696649894767145524911 233083044974842150718287367)
      ·
        refine ⟨349624567462263226077431051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233083044974842150718287367 349624567462263226077431051)
        ·
          refine ⟨524436851193394839116146577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349624567462263226077431051 524436851193394839116146577)
          ·
            refine ⟨393327638395046129337109933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524436851193394839116146577 393327638395046129337109933)
            ·
              refine ⟨147497864398142298501416225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393327638395046129337109933 147497864398142298501416225)
              ·
                refine ⟨110623398298606723876062169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147497864398142298501416225 110623398298606723876062169)
                ·
                  refine ⟨82967548723955042907046627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110623398298606723876062169 82967548723955042907046627)
                  ·
                    refine ⟨124451323085932564360569941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82967548723955042907046627 124451323085932564360569941)
                    ·
                      refine ⟨1458413942413272238600429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 124451323085932564360569941 1458413942413272238600429)
                      ·
                        rfl

theorem cell23_2840251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_2840251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840251 prefixEnd_2840251 := by exact prefixLift 2840251
  have htrace : WordTrace (prefixWord ++ tailWord_2840251) baseStart_2840251 baseEnd_2840251 := by
    simpa [prefixWord, tailWord_2840251, baseEnd_2840251] using wordTrace_append hprefix tailTrace_2840251
  have hstable : (prefixWord ++ tailWord_2840251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840251).length < 2 ^ (prefixWord ++ tailWord_2840251).sum := by decide
  have hdescent : baseEnd_2840251 < baseStart_2840251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840276 : List Nat := [2, 4, 1, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_2840276 : Nat := 118140960795 + 2840276 * 2 ^ 59
def prefixEnd_2840276 : Nat := 4983230072969 + 3 ^ 40 * 2840276 * 2
def baseEnd_2840276 : Nat := 1458426779429634640787815

theorem tailTrace_2840276 : CollatzResearch.WordTrace tailWord_2840276 prefixEnd_2840276 1458426779429634640787815 := by
  unfold tailWord_2840276
  simp only [CollatzResearch.WordTrace]
  refine ⟨51796688129086303683338341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69062250838781738244451121 51796688129086303683338341)
  ·
    refine ⟨9711879024203681940625939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51796688129086303683338341 9711879024203681940625939)
    ·
      refine ⟨14567818536305522910938909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9711879024203681940625939 14567818536305522910938909)
      ·
        refine ⟨5462931951114571091602091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14567818536305522910938909 5462931951114571091602091)
        ·
          refine ⟨8194397926671856637403137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5462931951114571091602091 8194397926671856637403137)
          ·
            refine ⟨6145798445003892478052353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8194397926671856637403137 6145798445003892478052353)
            ·
              refine ⟨4609348833752919358539265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6145798445003892478052353 4609348833752919358539265)
              ·
                refine ⟨3457011625314689518904449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4609348833752919358539265 3457011625314689518904449)
                ·
                  refine ⟨2592758718986017139178337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3457011625314689518904449 2592758718986017139178337)
                  ·
                    refine ⟨1944569039239512854383753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2592758718986017139178337 1944569039239512854383753)
                    ·
                      refine ⟨1458426779429634640787815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1944569039239512854383753 1458426779429634640787815)
                      ·
                        rfl

theorem cell23_2840276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_2840276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840276 prefixEnd_2840276 := by exact prefixLift 2840276
  have htrace : WordTrace (prefixWord ++ tailWord_2840276) baseStart_2840276 baseEnd_2840276 := by
    simpa [prefixWord, tailWord_2840276, baseEnd_2840276] using wordTrace_append hprefix tailTrace_2840276
  have hstable : (prefixWord ++ tailWord_2840276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840276).length < 2 ^ (prefixWord ++ tailWord_2840276).sum := by decide
  have hdescent : baseEnd_2840276 < baseStart_2840276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840282 : List Nat := [3, 1, 1, 2, 2, 3, 4, 2, 5]
def baseStart_2840282 : Nat := 118140960795 + 2840282 * 2 ^ 59
def prefixEnd_2840282 : Nat := 4983230072969 + 3 ^ 40 * 2840282 * 2
def baseEnd_2840282 : Nat := 162047762257062401923643

theorem tailTrace_2840282 : CollatzResearch.WordTrace tailWord_2840282 prefixEnd_2840282 162047762257062401923643 := by
  unfold tailWord_2840282
  simp only [CollatzResearch.WordTrace]
  refine ⟨25898398774037717597848775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69062396730767246927596733 25898398774037717597848775)
  ·
    refine ⟨38847598161056576396773163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25898398774037717597848775 38847598161056576396773163)
    ·
      refine ⟨58271397241584864595159745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38847598161056576396773163 58271397241584864595159745)
      ·
        refine ⟨43703547931188648446369809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58271397241584864595159745 43703547931188648446369809)
        ·
          refine ⟨32777660948391486334777357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43703547931188648446369809 32777660948391486334777357)
          ·
            refine ⟨12291622855646807375541509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32777660948391486334777357 12291622855646807375541509)
            ·
              refine ⟨2304679285433776382914033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12291622855646807375541509 2304679285433776382914033)
              ·
                refine ⟨1728509464075332287185525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2304679285433776382914033 1728509464075332287185525)
                ·
                  refine ⟨162047762257062401923643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1728509464075332287185525 162047762257062401923643)
                  ·
                    rfl

theorem cell23_2840282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 5].length) (baseStart_2840282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840282 prefixEnd_2840282 := by exact prefixLift 2840282
  have htrace : WordTrace (prefixWord ++ tailWord_2840282) baseStart_2840282 baseEnd_2840282 := by
    simpa [prefixWord, tailWord_2840282, baseEnd_2840282] using wordTrace_append hprefix tailTrace_2840282
  have hstable : (prefixWord ++ tailWord_2840282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840282).length < 2 ^ (prefixWord ++ tailWord_2840282).sum := by decide
  have hdescent : baseEnd_2840282 < baseStart_2840282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840288 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 5]
def baseStart_2840288 : Nat := 118140960795 + 2840288 * 2 ^ 59
def prefixEnd_2840288 : Nat := 4983230072969 + 3 ^ 40 * 2840288 * 2
def baseEnd_2840288 : Nat := 1458432941197488593837759

theorem tailTrace_2840288 : CollatzResearch.WordTrace tailWord_2840288 prefixEnd_2840288 1458432941197488593837759 := by
  unfold tailWord_2840288
  simp only [CollatzResearch.WordTrace]
  refine ⟨51796906967064566708056759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69062542622752755610742345 51796906967064566708056759)
  ·
    refine ⟨77695360450596850062085139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51796906967064566708056759 77695360450596850062085139)
    ·
      refine ⟨116543040675895275093127709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77695360450596850062085139 116543040675895275093127709)
      ·
        refine ⟨43703640253460728159922891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116543040675895275093127709 43703640253460728159922891)
        ·
          refine ⟨65555460380191092239884337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43703640253460728159922891 65555460380191092239884337)
          ·
            refine ⟨49166595285143319179913253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65555460380191092239884337 49166595285143319179913253)
            ·
              refine ⟨9218736615964372346233735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49166595285143319179913253 9218736615964372346233735)
              ·
                refine ⟨13828104923946558519350603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9218736615964372346233735 13828104923946558519350603)
                ·
                  refine ⟨20742157385919837779025905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13828104923946558519350603 20742157385919837779025905)
                  ·
                    refine ⟨15556618039439878334269429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20742157385919837779025905 15556618039439878334269429)
                    ·
                      refine ⟨1458432941197488593837759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15556618039439878334269429 1458432941197488593837759)
                      ·
                        rfl

theorem cell23_2840288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_2840288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840288 prefixEnd_2840288 := by exact prefixLift 2840288
  have htrace : WordTrace (prefixWord ++ tailWord_2840288) baseStart_2840288 baseEnd_2840288 := by
    simpa [prefixWord, tailWord_2840288, baseEnd_2840288] using wordTrace_append hprefix tailTrace_2840288
  have hstable : (prefixWord ++ tailWord_2840288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840288).length < 2 ^ (prefixWord ++ tailWord_2840288).sum := by decide
  have hdescent : baseEnd_2840288 < baseStart_2840288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840328 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2840328 : Nat := 118140960795 + 2840328 * 2 ^ 59
def prefixEnd_2840328 : Nat := 4983230072969 + 3 ^ 40 * 2840328 * 2
def baseEnd_2840328 : Nat := 1458453480423668437337575

theorem tailTrace_2840328 : CollatzResearch.WordTrace tailWord_2840328 prefixEnd_2840328 1458453480423668437337575 := by
  unfold tailWord_2840328
  simp only [CollatzResearch.WordTrace]
  refine ⟨51797636426992110123784819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69063515235989480165046425 51797636426992110123784819)
  ·
    refine ⟨77696454640488165185677229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51797636426992110123784819 77696454640488165185677229)
    ·
      refine ⟨29136170490183061944628961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77696454640488165185677229 29136170490183061944628961)
      ·
        refine ⟨21852127867637296458471721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29136170490183061944628961 21852127867637296458471721)
        ·
          refine ⟨16389095900727972343853791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21852127867637296458471721 16389095900727972343853791)
          ·
            refine ⟨24583643851091958515780687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16389095900727972343853791 24583643851091958515780687)
            ·
              refine ⟨36875465776637937773671031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24583643851091958515780687 36875465776637937773671031)
              ·
                refine ⟨55313198664956906660506547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36875465776637937773671031 55313198664956906660506547)
                ·
                  refine ⟨82969797997435359990759821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55313198664956906660506547 82969797997435359990759821)
                  ·
                    refine ⟨31113674249038259996534933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82969797997435359990759821 31113674249038259996534933)
                    ·
                      refine ⟨1458453480423668437337575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31113674249038259996534933 1458453480423668437337575)
                      ·
                        rfl

theorem cell23_2840328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2840328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840328 prefixEnd_2840328 := by exact prefixLift 2840328
  have htrace : WordTrace (prefixWord ++ tailWord_2840328) baseStart_2840328 baseEnd_2840328 := by
    simpa [prefixWord, tailWord_2840328, baseEnd_2840328] using wordTrace_append hprefix tailTrace_2840328
  have hstable : (prefixWord ++ tailWord_2840328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840328).length < 2 ^ (prefixWord ++ tailWord_2840328).sum := by decide
  have hdescent : baseEnd_2840328 < baseStart_2840328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840392 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 4, 3, 2]
def baseStart_2840392 : Nat := 118140960795 + 2840392 * 2 ^ 59
def prefixEnd_2840392 : Nat := 4983230072969 + 3 ^ 40 * 2840392 * 2
def baseEnd_2840392 : Nat := 1458486343185556186937281

theorem tailTrace_2840392 : CollatzResearch.WordTrace tailWord_2840392 prefixEnd_2840392 1458486343185556186937281 := by
  unfold tailWord_2840392
  simp only [CollatzResearch.WordTrace]
  refine ⟨51798803562876179588949715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69065071417168239451932953 51798803562876179588949715)
  ·
    refine ⟨77698205344314269383424573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51798803562876179588949715 77698205344314269383424573)
    ·
      refine ⟨29136827004117851018784215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77698205344314269383424573 29136827004117851018784215)
      ·
        refine ⟨43705240506176776528176323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29136827004117851018784215 43705240506176776528176323)
        ·
          refine ⟨65557860759265164792264485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43705240506176776528176323 65557860759265164792264485)
          ·
            refine ⟨12292098892362218398549591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65557860759265164792264485 12292098892362218398549591)
            ·
              refine ⟨18438148338543327597824387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12292098892362218398549591 18438148338543327597824387)
              ·
                refine ⟨27657222507814991396736581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18438148338543327597824387 27657222507814991396736581)
                ·
                  refine ⟨5185729220215310886888109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27657222507814991396736581 5185729220215310886888109)
                  ·
                    refine ⟨1944648457580741582583041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5185729220215310886888109 1944648457580741582583041)
                    ·
                      refine ⟨1458486343185556186937281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1944648457580741582583041 1458486343185556186937281)
                      ·
                        rfl

theorem cell23_2840392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_2840392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840392 prefixEnd_2840392 := by exact prefixLift 2840392
  have htrace : WordTrace (prefixWord ++ tailWord_2840392) baseStart_2840392 baseEnd_2840392 := by
    simpa [prefixWord, tailWord_2840392, baseEnd_2840392] using wordTrace_append hprefix tailTrace_2840392
  have hstable : (prefixWord ++ tailWord_2840392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840392).length < 2 ^ (prefixWord ++ tailWord_2840392).sum := by decide
  have hdescent : baseEnd_2840392 < baseStart_2840392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840419 : List Nat := [1, 1, 1, 5, 4, 2, 1, 2, 1, 5]
def baseStart_2840419 : Nat := 118140960795 + 2840419 * 2 ^ 59
def prefixEnd_2840419 : Nat := 4983230072969 + 3 ^ 40 * 2840419 * 2
def baseEnd_2840419 : Nat := 486166735721075860433219

theorem tailTrace_2840419 : CollatzResearch.WordTrace tailWord_2840419 prefixEnd_2840419 486166735721075860433219 := by
  unfold tailWord_2840419
  simp only [CollatzResearch.WordTrace]
  refine ⟨103598591896654542789132311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69065727931103028526088207 103598591896654542789132311)
  ·
    refine ⟨155397887844981814183698467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103598591896654542789132311 155397887844981814183698467)
    ·
      refine ⟨233096831767472721275547701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155397887844981814183698467 233096831767472721275547701)
      ·
        refine ⟨21852827978200567619582597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 233096831767472721275547701 21852827978200567619582597)
        ·
          refine ⟨4097405245912606428671737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21852827978200567619582597 4097405245912606428671737)
          ·
            refine ⟨3073053934434454821503803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4097405245912606428671737 3073053934434454821503803)
            ·
              refine ⟨4609580901651682232255705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3073053934434454821503803 4609580901651682232255705)
              ·
                refine ⟨3457185676238761674191779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4609580901651682232255705 3457185676238761674191779)
                ·
                  refine ⟨5185778514358142511287669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457185676238761674191779 5185778514358142511287669)
                  ·
                    refine ⟨486166735721075860433219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5185778514358142511287669 486166735721075860433219)
                    ·
                      rfl

theorem cell23_2840419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 5].length) (baseStart_2840419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840419 prefixEnd_2840419 := by exact prefixLift 2840419
  have htrace : WordTrace (prefixWord ++ tailWord_2840419) baseStart_2840419 baseEnd_2840419 := by
    simpa [prefixWord, tailWord_2840419, baseEnd_2840419] using wordTrace_append hprefix tailTrace_2840419
  have hstable : (prefixWord ++ tailWord_2840419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840419).length < 2 ^ (prefixWord ++ tailWord_2840419).sum := by decide
  have hdescent : baseEnd_2840419 < baseStart_2840419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840442 : List Nat := [3, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3]
def baseStart_2840442 : Nat := 118140960795 + 2840442 * 2 ^ 59
def prefixEnd_2840442 : Nat := 4983230072969 + 3 ^ 40 * 2840442 * 2
def baseEnd_2840442 : Nat := 1458512017218280991312051

theorem tailTrace_2840442 : CollatzResearch.WordTrace tailWord_2840442 prefixEnd_2840442 1458512017218280991312051 := by
  unfold tailWord_2840442
  simp only [CollatzResearch.WordTrace]
  refine ⟨25899857693892804429304895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69066287183714145144813053 25899857693892804429304895)
  ·
    refine ⟨38849786540839206643957343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25899857693892804429304895 38849786540839206643957343)
    ·
      refine ⟨58274679811258809965936015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38849786540839206643957343 58274679811258809965936015)
      ·
        refine ⟨87412019716888214948904023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58274679811258809965936015 87412019716888214948904023)
        ·
          refine ⟨131118029575332322423356035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87412019716888214948904023 131118029575332322423356035)
          ·
            refine ⟨196677044362998483635034053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131118029575332322423356035 196677044362998483635034053)
            ·
              refine ⟨36876945818062215681568885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196677044362998483635034053 36876945818062215681568885)
              ·
                refine ⟨3457213670443332720147083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36876945818062215681568885 3457213670443332720147083)
                ·
                  refine ⟨5185820505664999080220625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457213670443332720147083 5185820505664999080220625)
                  ·
                    refine ⟨3889365379248749310165469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5185820505664999080220625 3889365379248749310165469)
                    ·
                      refine ⟨1458512017218280991312051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3889365379248749310165469 1458512017218280991312051)
                      ·
                        rfl

theorem cell23_2840442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_2840442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840442 prefixEnd_2840442 := by exact prefixLift 2840442
  have htrace : WordTrace (prefixWord ++ tailWord_2840442) baseStart_2840442 baseEnd_2840442 := by
    simpa [prefixWord, tailWord_2840442, baseEnd_2840442] using wordTrace_append hprefix tailTrace_2840442
  have hstable : (prefixWord ++ tailWord_2840442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840442).length < 2 ^ (prefixWord ++ tailWord_2840442).sum := by decide
  have hdescent : baseEnd_2840442 < baseStart_2840442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840499 : List Nat := [1, 1, 1, 2, 3, 1, 5, 3, 1, 3, 2]
def baseStart_2840499 : Nat := 118140960795 + 2840499 * 2 ^ 59
def prefixEnd_2840499 : Nat := 4983230072969 + 3 ^ 40 * 2840499 * 2
def baseEnd_2840499 : Nat := 1458541285615587268299289

theorem tailTrace_2840499 : CollatzResearch.WordTrace tailWord_2840499 prefixEnd_2840499 1458541285615587268299289 := by
  unfold tailWord_2840499
  simp only [CollatzResearch.WordTrace]
  refine ⟨103601509736364716452044551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69067673157576477634696367 103601509736364716452044551)
  ·
    refine ⟨155402264604547074678066827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103601509736364716452044551 155402264604547074678066827)
    ·
      refine ⟨233103396906820612017100241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155402264604547074678066827 233103396906820612017100241)
      ·
        refine ⟨174827547680115459012825181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233103396906820612017100241 174827547680115459012825181)
        ·
          refine ⟨65560330380043297129809443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174827547680115459012825181 65560330380043297129809443)
          ·
            refine ⟨98340495570064945694714165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65560330380043297129809443 98340495570064945694714165)
            ·
              refine ⟨9219421459693588658879453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98340495570064945694714165 9219421459693588658879453)
              ·
                refine ⟨3457283047385095747079795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9219421459693588658879453 3457283047385095747079795)
                ·
                  refine ⟨5185924571077643620619693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457283047385095747079795 5185924571077643620619693)
                  ·
                    refine ⟨1944721714154116357732385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5185924571077643620619693 1944721714154116357732385)
                    ·
                      refine ⟨1458541285615587268299289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1944721714154116357732385 1458541285615587268299289)
                      ·
                        rfl

theorem cell23_2840499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 3, 2].length) (baseStart_2840499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840499 prefixEnd_2840499 := by exact prefixLift 2840499
  have htrace : WordTrace (prefixWord ++ tailWord_2840499) baseStart_2840499 baseEnd_2840499 := by
    simpa [prefixWord, tailWord_2840499, baseEnd_2840499] using wordTrace_append hprefix tailTrace_2840499
  have hstable : (prefixWord ++ tailWord_2840499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840499).length < 2 ^ (prefixWord ++ tailWord_2840499).sum := by decide
  have hdescent : baseEnd_2840499 < baseStart_2840499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840500 : List Nat := [2, 5, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_2840500 : Nat := 118140960795 + 2840500 * 2 ^ 59
def prefixEnd_2840500 : Nat := 4983230072969 + 3 ^ 40 * 2840500 * 2
def baseEnd_2840500 : Nat := 486180599698747254795595

theorem tailTrace_2840500 : CollatzResearch.WordTrace tailWord_2840500 prefixEnd_2840500 486180599698747254795595 := by
  unfold tailWord_2840500
  simp only [CollatzResearch.WordTrace]
  refine ⟨51800773104680546811415477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69067697472907395748553969 51800773104680546811415477)
  ·
    refine ⟨4856322478563801263570201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51800773104680546811415477 4856322478563801263570201)
    ·
      refine ⟨3642241858922850947677651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4856322478563801263570201 3642241858922850947677651)
      ·
        refine ⟨5463362788384276421516477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3642241858922850947677651 5463362788384276421516477)
        ·
          refine ⟨2048761045644103658068679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5463362788384276421516477 2048761045644103658068679)
          ·
            refine ⟨3073141568466155487103019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048761045644103658068679 3073141568466155487103019)
            ·
              refine ⟨4609712352699233230654529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3073141568466155487103019 4609712352699233230654529)
              ·
                refine ⟨3457284264524424922990897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4609712352699233230654529 3457284264524424922990897)
                ·
                  refine ⟨2592963198393318692243173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3457284264524424922990897 2592963198393318692243173)
                  ·
                    refine ⟨486180599698747254795595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2592963198393318692243173 486180599698747254795595)
                    ·
                      rfl

theorem cell23_2840500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_2840500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840500 prefixEnd_2840500 := by exact prefixLift 2840500
  have htrace : WordTrace (prefixWord ++ tailWord_2840500) baseStart_2840500 baseEnd_2840500 := by
    simpa [prefixWord, tailWord_2840500, baseEnd_2840500] using wordTrace_append hprefix tailTrace_2840500
  have hstable : (prefixWord ++ tailWord_2840500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840500).length < 2 ^ (prefixWord ++ tailWord_2840500).sum := by decide
  have hdescent : baseEnd_2840500 < baseStart_2840500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840505 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 4, 6]
def baseStart_2840505 : Nat := 118140960795 + 2840505 * 2 ^ 59
def prefixEnd_2840505 : Nat := 4983230072969 + 3 ^ 40 * 2840505 * 2
def baseEnd_2840505 : Nat := 486181455499838081608087

theorem tailTrace_2840505 : CollatzResearch.WordTrace tailWord_2840505 prefixEnd_2840505 486181455499838081608087 := by
  unfold tailWord_2840505
  simp only [CollatzResearch.WordTrace]
  refine ⟨103601728574342979476762969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69067819049561986317841979 103601728574342979476762969)
  ·
    refine ⟨77701296430757234607572227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103601728574342979476762969 77701296430757234607572227)
    ·
      refine ⟨116551944646135851911358341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77701296430757234607572227 116551944646135851911358341)
      ·
        refine ⟨21853489621150472233379689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116551944646135851911358341 21853489621150472233379689)
        ·
          refine ⟨16390117215862854175034767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21853489621150472233379689 16390117215862854175034767)
          ·
            refine ⟨24585175823794281262552151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16390117215862854175034767 24585175823794281262552151)
            ·
              refine ⟨36877763735691421893828227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24585175823794281262552151 36877763735691421893828227)
              ·
                refine ⟨55316645603537132840742341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36877763735691421893828227 55316645603537132840742341)
                ·
                  refine ⟨10371871050663212407639189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55316645603537132840742341 10371871050663212407639189)
                  ·
                    refine ⟨486181455499838081608087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10371871050663212407639189 486181455499838081608087)
                    ·
                      rfl

theorem cell23_2840505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_2840505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840505 prefixEnd_2840505 := by exact prefixLift 2840505
  have htrace : WordTrace (prefixWord ++ tailWord_2840505) baseStart_2840505 baseEnd_2840505 := by
    simpa [prefixWord, tailWord_2840505, baseEnd_2840505] using wordTrace_append hprefix tailTrace_2840505
  have hstable : (prefixWord ++ tailWord_2840505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840505).length < 2 ^ (prefixWord ++ tailWord_2840505).sum := by decide
  have hdescent : baseEnd_2840505 < baseStart_2840505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840532 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_2840532 : Nat := 118140960795 + 2840532 * 2 ^ 59
def prefixEnd_2840532 : Nat := 4983230072969 + 3 ^ 40 * 2840532 * 2
def baseEnd_2840532 : Nat := 1458558230477185639186637

theorem tailTrace_2840532 : CollatzResearch.WordTrace tailWord_2840532 prefixEnd_2840532 1458558230477185639186637 := by
  unfold tailWord_2840532
  simp only [CollatzResearch.WordTrace]
  refine ⟨51801356672622581543997925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69068475563496775391997233 51801356672622581543997925)
  ·
    refine ⟨9712754376116734039499611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51801356672622581543997925 9712754376116734039499611)
    ·
      refine ⟨14569131564175101059249417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9712754376116734039499611 14569131564175101059249417)
      ·
        refine ⟨10926848673131325794437063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14569131564175101059249417 10926848673131325794437063)
        ·
          refine ⟨16390273009696988691655595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10926848673131325794437063 16390273009696988691655595)
          ·
            refine ⟨24585409514545483037483393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16390273009696988691655595 24585409514545483037483393)
            ·
              refine ⟨18439057135909112278112545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24585409514545483037483393 18439057135909112278112545)
              ·
                refine ⟨13829292851931834208584409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18439057135909112278112545 13829292851931834208584409)
                ·
                  refine ⟨10371969638948875656438307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13829292851931834208584409 10371969638948875656438307)
                  ·
                    refine ⟨15557954458423313484657461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10371969638948875656438307 15557954458423313484657461)
                    ·
                      refine ⟨1458558230477185639186637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15557954458423313484657461 1458558230477185639186637)
                      ·
                        rfl

theorem cell23_2840532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_2840532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840532 prefixEnd_2840532 := by exact prefixLift 2840532
  have htrace : WordTrace (prefixWord ++ tailWord_2840532) baseStart_2840532 baseEnd_2840532 := by
    simpa [prefixWord, tailWord_2840532, baseEnd_2840532] using wordTrace_append hprefix tailTrace_2840532
  have hstable : (prefixWord ++ tailWord_2840532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840532).length < 2 ^ (prefixWord ++ tailWord_2840532).sum := by decide
  have hdescent : baseEnd_2840532 < baseStart_2840532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840535 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 7]
def baseStart_2840535 : Nat := 118140960795 + 2840535 * 2 ^ 59
def prefixEnd_2840535 : Nat := 4983230072969 + 3 ^ 40 * 2840535 * 2
def baseEnd_2840535 : Nat := 162062196768794347494347

theorem tailTrace_2840535 : CollatzResearch.WordTrace tailWord_2840535 prefixEnd_2840535 162062196768794347494347 := by
  unfold tailWord_2840535
  simp only [CollatzResearch.WordTrace]
  refine ⟨103602822764234294600355059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69068548509489529733570039 103602822764234294600355059)
  ·
    refine ⟨155404234146351441900532589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103602822764234294600355059 155404234146351441900532589)
    ·
      refine ⟨58276587804881790712699721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155404234146351441900532589 58276587804881790712699721)
      ·
        refine ⟨43707440853661343034524791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58276587804881790712699721 43707440853661343034524791)
        ·
          refine ⟨65561161280492014551787187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43707440853661343034524791 65561161280492014551787187)
          ·
            refine ⟨98341741920738021827680781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65561161280492014551787187 98341741920738021827680781)
            ·
              refine ⟨36878153220276758185380293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98341741920738021827680781 36878153220276758185380293)
              ·
                refine ⟨6914653728801892159758805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36878153220276758185380293 6914653728801892159758805)
                ·
                  refine ⟨162062196768794347494347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6914653728801892159758805 162062196768794347494347)
                  ·
                    rfl

theorem cell23_2840535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 7].length) (baseStart_2840535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840535 prefixEnd_2840535 := by exact prefixLift 2840535
  have htrace : WordTrace (prefixWord ++ tailWord_2840535) baseStart_2840535 baseEnd_2840535 := by
    simpa [prefixWord, tailWord_2840535, baseEnd_2840535] using wordTrace_append hprefix tailTrace_2840535
  have hstable : (prefixWord ++ tailWord_2840535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840535).length < 2 ^ (prefixWord ++ tailWord_2840535).sum := by decide
  have hdescent : baseEnd_2840535 < baseStart_2840535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840580 : List Nat := [2, 3, 2, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2840580 : Nat := 118140960795 + 2840580 * 2 ^ 59
def prefixEnd_2840580 : Nat := 4983230072969 + 3 ^ 40 * 2840580 * 2
def baseEnd_2840580 : Nat := 1458582877548601451386417

theorem tailTrace_2840580 : CollatzResearch.WordTrace tailWord_2840580 prefixEnd_2840580 1458582877548601451386417 := by
  unfold tailWord_2840580
  simp only [CollatzResearch.WordTrace]
  refine ⟨51802232024535633642871597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69069642699380844857162129 51802232024535633642871597)
  ·
    refine ⟨19425837009200862616076849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51802232024535633642871597 19425837009200862616076849)
    ·
      refine ⟨14569377756900646962057637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19425837009200862616076849 14569377756900646962057637)
      ·
        refine ⟨2731758329418871305385807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14569377756900646962057637 2731758329418871305385807)
        ·
          refine ⟨4097637494128306958078711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731758329418871305385807 4097637494128306958078711)
          ·
            refine ⟨6146456241192460437118067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4097637494128306958078711 6146456241192460437118067)
            ·
              refine ⟨9219684361788690655677101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6146456241192460437118067 9219684361788690655677101)
              ·
                refine ⟨3457381635670758995878913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9219684361788690655677101 3457381635670758995878913)
                ·
                  refine ⟨2593036226753069246909185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3457381635670758995878913 2593036226753069246909185)
                  ·
                    refine ⟨1944777170064801935181889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2593036226753069246909185 1944777170064801935181889)
                    ·
                      refine ⟨1458582877548601451386417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1944777170064801935181889 1458582877548601451386417)
                      ·
                        rfl

theorem cell23_2840580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2840580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840580 prefixEnd_2840580 := by exact prefixLift 2840580
  have htrace : WordTrace (prefixWord ++ tailWord_2840580) baseStart_2840580 baseEnd_2840580 := by
    simpa [prefixWord, tailWord_2840580, baseEnd_2840580] using wordTrace_append hprefix tailTrace_2840580
  have hstable : (prefixWord ++ tailWord_2840580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840580).length < 2 ^ (prefixWord ++ tailWord_2840580).sum := by decide
  have hdescent : baseEnd_2840580 < baseStart_2840580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840595 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 2, 8]
def baseStart_2840595 : Nat := 118140960795 + 2840595 * 2 ^ 59
def prefixEnd_2840595 : Nat := 4983230072969 + 3 ^ 40 * 2840595 * 2
def baseEnd_2840595 : Nat := 486196859919472964232949

theorem tailTrace_2840595 : CollatzResearch.WordTrace tailWord_2840595 prefixEnd_2840595 486196859919472964232949 := by
  unfold tailWord_2840595
  simp only [CollatzResearch.WordTrace]
  refine ⟨103605011144016924847539239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69070007429344616565026159 103605011144016924847539239)
  ·
    refine ⟨155407516716025387271308859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103605011144016924847539239 155407516716025387271308859)
    ·
      refine ⟨233111275074038080906963289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155407516716025387271308859 233111275074038080906963289)
      ·
        refine ⟨174833456305528560680222467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233111275074038080906963289 174833456305528560680222467)
        ·
          refine ⟨262250184458292841020333701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174833456305528560680222467 262250184458292841020333701)
          ·
            refine ⟨49171909585929907691312569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262250184458292841020333701 49171909585929907691312569)
            ·
              refine ⟨36878932189447430768484427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49171909585929907691312569 36878932189447430768484427)
              ·
                refine ⟨55318398284171146152726641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36878932189447430768484427 55318398284171146152726641)
                ·
                  refine ⟨41488798713128359614544981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55318398284171146152726641 41488798713128359614544981)
                  ·
                    refine ⟨486196859919472964232949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41488798713128359614544981 486196859919472964232949)
                    ·
                      rfl

theorem cell23_2840595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 8].length) (baseStart_2840595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840595 prefixEnd_2840595 := by exact prefixLift 2840595
  have htrace : WordTrace (prefixWord ++ tailWord_2840595) baseStart_2840595 baseEnd_2840595 := by
    simpa [prefixWord, tailWord_2840595, baseEnd_2840595] using wordTrace_append hprefix tailTrace_2840595
  have hstable : (prefixWord ++ tailWord_2840595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840595).length < 2 ^ (prefixWord ++ tailWord_2840595).sum := by decide
  have hdescent : baseEnd_2840595 < baseStart_2840595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840749 : List Nat := [1, 5, 2, 1, 2, 1, 1, 10]
def baseStart_2840749 : Nat := 118140960795 + 2840749 * 2 ^ 59
def prefixEnd_2840749 : Nat := 4983230072969 + 3 ^ 40 * 2840749 * 2
def baseEnd_2840749 : Nat := 54024802065896714450857

theorem tailTrace_2840749 : CollatzResearch.WordTrace tailWord_2840749 prefixEnd_2840749 54024802065896714450857 := by
  unfold tailWord_2840749
  simp only [CollatzResearch.WordTrace]
  refine ⟨103610627985459009148645301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69073751990306006099096867 103610627985459009148645301)
  ·
    refine ⟨9713496373636782107685497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103610627985459009148645301 9713496373636782107685497)
    ·
      refine ⟨7285122280227586580764123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9713496373636782107685497 7285122280227586580764123)
      ·
        refine ⟨10927683420341379871146185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7285122280227586580764123 10927683420341379871146185)
        ·
          refine ⟨8195762565256034903359639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10927683420341379871146185 8195762565256034903359639)
          ·
            refine ⟨12293643847884052355039459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8195762565256034903359639 12293643847884052355039459)
            ·
              refine ⟨18440465771826078532559189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12293643847884052355039459 18440465771826078532559189)
              ·
                refine ⟨54024802065896714450857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18440465771826078532559189 54024802065896714450857)
                ·
                  rfl

theorem cell23_2840749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 10].length) (baseStart_2840749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840749 prefixEnd_2840749 := by exact prefixLift 2840749
  have htrace : WordTrace (prefixWord ++ tailWord_2840749) baseStart_2840749 baseEnd_2840749 := by
    simpa [prefixWord, tailWord_2840749, baseEnd_2840749] using wordTrace_append hprefix tailTrace_2840749
  have hstable : (prefixWord ++ tailWord_2840749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840749).length < 2 ^ (prefixWord ++ tailWord_2840749).sum := by decide
  have hdescent : baseEnd_2840749 < baseStart_2840749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840753 : List Nat := [1, 2, 2, 5, 2, 1, 1, 3, 2, 4]
def baseStart_2840753 : Nat := 118140960795 + 2840753 * 2 ^ 59
def prefixEnd_2840753 : Nat := 4983230072969 + 3 ^ 40 * 2840753 * 2
def baseEnd_2840753 : Nat := 486223903233943091507707

theorem tailTrace_2840753 : CollatzResearch.WordTrace tailWord_2840753 prefixEnd_2840753 486223903233943091507707 := by
  unfold tailWord_2840753
  simp only [CollatzResearch.WordTrace]
  refine ⟨103610773877444517831790913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69073849251629678554527275 103610773877444517831790913)
  ·
    refine ⟨77708080408083388373843185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103610773877444517831790913 77708080408083388373843185)
    ·
      refine ⟨58281060306062541280382389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77708080408083388373843185 58281060306062541280382389)
      ·
        refine ⟨5463849403693363245035849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58281060306062541280382389 5463849403693363245035849)
        ·
          refine ⟨4097887052770022433776887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5463849403693363245035849 4097887052770022433776887)
          ·
            refine ⟨6146830579155033650665331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4097887052770022433776887 6146830579155033650665331)
            ·
              refine ⟨9220245868732550475997997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6146830579155033650665331 9220245868732550475997997)
              ·
                refine ⟨3457592200774706428499249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9220245868732550475997997 3457592200774706428499249)
                ·
                  refine ⟨2593194150581029821374437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3457592200774706428499249 2593194150581029821374437)
                  ·
                    refine ⟨486223903233943091507707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2593194150581029821374437 486223903233943091507707)
                    ·
                      rfl

theorem cell23_2840753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_2840753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840753 prefixEnd_2840753 := by exact prefixLift 2840753
  have htrace : WordTrace (prefixWord ++ tailWord_2840753) baseStart_2840753 baseEnd_2840753 := by
    simpa [prefixWord, tailWord_2840753, baseEnd_2840753] using wordTrace_append hprefix tailTrace_2840753
  have hstable : (prefixWord ++ tailWord_2840753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840753).length < 2 ^ (prefixWord ++ tailWord_2840753).sum := by decide
  have hdescent : baseEnd_2840753 < baseStart_2840753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840780 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 1, 1, 5]
def baseStart_2840780 : Nat := 118140960795 + 2840780 * 2 ^ 59
def prefixEnd_2840780 : Nat := 4983230072969 + 3 ^ 40 * 2840780 * 2
def baseEnd_2840780 : Nat := 1458685573679500668885497

theorem tailTrace_2840780 : CollatzResearch.WordTrace tailWord_2840780 prefixEnd_2840780 1458685573679500668885497 := by
  unfold tailWord_2840780
  simp only [CollatzResearch.WordTrace]
  refine ⟨51805879324173350721511897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69074505765564467628682529 51805879324173350721511897)
  ·
    refine ⟨38854409493130013041133923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51805879324173350721511897 38854409493130013041133923)
    ·
      refine ⟨58281614239695019561700885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38854409493130013041133923 58281614239695019561700885)
      ·
        refine ⟨2731950667485704041954729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58281614239695019561700885 2731950667485704041954729)
        ·
          refine ⟨2048963000614278031466047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2731950667485704041954729 2048963000614278031466047)
          ·
            refine ⟨3073444500921417047199071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048963000614278031466047 3073444500921417047199071)
            ·
              refine ⟨4610166751382125570798607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3073444500921417047199071 4610166751382125570798607)
              ·
                refine ⟨6915250127073188356197911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4610166751382125570798607 6915250127073188356197911)
                ·
                  refine ⟨10372875190609782534296867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6915250127073188356197911 10372875190609782534296867)
                  ·
                    refine ⟨15559312785914673801445301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10372875190609782534296867 15559312785914673801445301)
                    ·
                      refine ⟨1458685573679500668885497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15559312785914673801445301 1458685573679500668885497)
                      ·
                        rfl

theorem cell23_2840780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_2840780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840780 prefixEnd_2840780 := by exact prefixLift 2840780
  have htrace : WordTrace (prefixWord ++ tailWord_2840780) baseStart_2840780 baseEnd_2840780 := by
    simpa [prefixWord, tailWord_2840780, baseEnd_2840780] using wordTrace_append hprefix tailTrace_2840780
  have hstable : (prefixWord ++ tailWord_2840780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840780).length < 2 ^ (prefixWord ++ tailWord_2840780).sum := by decide
  have hdescent : baseEnd_2840780 < baseStart_2840780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840819 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 3]
def baseStart_2840819 : Nat := 118140960795 + 2840819 * 2 ^ 59
def prefixEnd_2840819 : Nat := 4983230072969 + 3 ^ 40 * 2840819 * 2
def baseEnd_2840819 : Nat := 1458705599425026016297817

theorem tailTrace_2840819 : CollatzResearch.WordTrace tailWord_2840819 prefixEnd_2840819 1458705599425026016297817 := by
  unfold tailWord_2840819
  simp only [CollatzResearch.WordTrace]
  refine ⟨103613181095205411103693511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69075454063470274069129007 103613181095205411103693511)
  ·
    refine ⟨155419771642808116655540267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103613181095205411103693511 155419771642808116655540267)
    ·
      refine ⟨233129657464212174983310401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155419771642808116655540267 233129657464212174983310401)
      ·
        refine ⟨174847243098159131237482801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233129657464212174983310401 174847243098159131237482801)
        ·
          refine ⟨131135432323619348428112101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174847243098159131237482801 131135432323619348428112101)
          ·
            refine ⟨24587893560678627830271019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131135432323619348428112101 24587893560678627830271019)
            ·
              refine ⟨36881840341017941745406529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24587893560678627830271019 36881840341017941745406529)
              ·
                refine ⟨27661380255763456309054897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36881840341017941745406529 27661380255763456309054897)
                ·
                  refine ⟨20746035191822592231791173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27661380255763456309054897 20746035191822592231791173)
                  ·
                    refine ⟨3889881598466736043460845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20746035191822592231791173 3889881598466736043460845)
                    ·
                      refine ⟨1458705599425026016297817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3889881598466736043460845 1458705599425026016297817)
                      ·
                        rfl

theorem cell23_2840819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 3].length) (baseStart_2840819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840819 prefixEnd_2840819 := by exact prefixLift 2840819
  have htrace : WordTrace (prefixWord ++ tailWord_2840819) baseStart_2840819 baseEnd_2840819 := by
    simpa [prefixWord, tailWord_2840819, baseEnd_2840819] using wordTrace_append hprefix tailTrace_2840819
  have hstable : (prefixWord ++ tailWord_2840819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840819).length < 2 ^ (prefixWord ++ tailWord_2840819).sum := by decide
  have hdescent : baseEnd_2840819 < baseStart_2840819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840833 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_2840833 : Nat := 118140960795 + 2840833 * 2 ^ 59
def prefixEnd_2840833 : Nat := 4983230072969 + 3 ^ 40 * 2840833 * 2
def baseEnd_2840833 : Nat := 1458712788154188961522753

theorem tailTrace_2840833 : CollatzResearch.WordTrace tailWord_2840833 prefixEnd_2840833 1458712788154188961522753 := by
  unfold tailWord_2840833
  simp only [CollatzResearch.WordTrace]
  refine ⟨103613691717154691494703153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69075794478103127663135435 103613691717154691494703153)
  ·
    refine ⟨77710268787866018621027365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103613691717154691494703153 77710268787866018621027365)
    ·
      refine ⟨14570675397724878491442631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77710268787866018621027365 14570675397724878491442631)
      ·
        refine ⟨21856013096587317737163947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14570675397724878491442631 21856013096587317737163947)
        ·
          refine ⟨32784019644880976605745921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21856013096587317737163947 32784019644880976605745921)
          ·
            refine ⟨24588014733660732454309441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32784019644880976605745921 24588014733660732454309441)
            ·
              refine ⟨18441011050245549340732081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24588014733660732454309441 18441011050245549340732081)
              ·
                refine ⟨13830758287684162005549061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18441011050245549340732081 13830758287684162005549061)
                ·
                  refine ⟨2593267178940780376040449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13830758287684162005549061 2593267178940780376040449)
                  ·
                    refine ⟨1944950384205585282030337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2593267178940780376040449 1944950384205585282030337)
                    ·
                      refine ⟨1458712788154188961522753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1944950384205585282030337 1458712788154188961522753)
                      ·
                        rfl

theorem cell23_2840833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_2840833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840833 prefixEnd_2840833 := by exact prefixLift 2840833
  have htrace : WordTrace (prefixWord ++ tailWord_2840833) baseStart_2840833 baseEnd_2840833 := by
    simpa [prefixWord, tailWord_2840833, baseEnd_2840833] using wordTrace_append hprefix tailTrace_2840833
  have hstable : (prefixWord ++ tailWord_2840833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840833).length < 2 ^ (prefixWord ++ tailWord_2840833).sum := by decide
  have hdescent : baseEnd_2840833 < baseStart_2840833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840856 : List Nat := [2, 1, 2, 3, 1, 2, 1, 6, 5]
def baseStart_2840856 : Nat := 118140960795 + 2840856 * 2 ^ 59
def prefixEnd_2840856 : Nat := 4983230072969 + 3 ^ 40 * 2840856 * 2
def baseEnd_2840856 : Nat := 162080510912138041281683

theorem tailTrace_2840856 : CollatzResearch.WordTrace tailWord_2840856 prefixEnd_2840856 162080510912138041281683 := by
  unfold tailWord_2840856
  simp only [CollatzResearch.WordTrace]
  refine ⟨51807265298035683211395211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69076353730714244281860281 51807265298035683211395211)
  ·
    refine ⟨77710897947053524817092817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51807265298035683211395211 77710897947053524817092817)
    ·
      refine ⟨58283173460290143612819613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77710897947053524817092817 58283173460290143612819613)
      ·
        refine ⟨21856190047608803854807355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58283173460290143612819613 21856190047608803854807355)
        ·
          refine ⟨32784285071413205782211033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21856190047608803854807355 32784285071413205782211033)
          ·
            refine ⟨24588213803559904336658275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32784285071413205782211033 24588213803559904336658275)
            ·
              refine ⟨36882320705339856504987413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24588213803559904336658275 36882320705339856504987413)
              ·
                refine ⟨1728858783062805773671285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36882320705339856504987413 1728858783062805773671285)
                ·
                  refine ⟨162080510912138041281683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1728858783062805773671285 162080510912138041281683)
                  ·
                    rfl

theorem cell23_2840856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 5].length) (baseStart_2840856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840856 prefixEnd_2840856 := by exact prefixLift 2840856
  have htrace : WordTrace (prefixWord ++ tailWord_2840856) baseStart_2840856 baseEnd_2840856 := by
    simpa [prefixWord, tailWord_2840856, baseEnd_2840856] using wordTrace_append hprefix tailTrace_2840856
  have hstable : (prefixWord ++ tailWord_2840856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840856).length < 2 ^ (prefixWord ++ tailWord_2840856).sum := by decide
  have hdescent : baseEnd_2840856 < baseStart_2840856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840876 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 2, 5, 2]
def baseStart_2840876 : Nat := 118140960795 + 2840876 * 2 ^ 59
def prefixEnd_2840876 : Nat := 4983230072969 + 3 ^ 40 * 2840876 * 2
def baseEnd_2840876 : Nat := 1458734867822332293285055

theorem tailTrace_2840876 : CollatzResearch.WordTrace tailWord_2840876 prefixEnd_2840876 1458734867822332293285055 := by
  unfold tailWord_2840876
  simp only [CollatzResearch.WordTrace]
  refine ⟨51807630027999454919259241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69076840037332606559012321 51807630027999454919259241)
  ·
    refine ⟨38855722520999591189444431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51807630027999454919259241 38855722520999591189444431)
    ·
      refine ⟨58283583781499386784166647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38855722520999591189444431 58283583781499386784166647)
      ·
        refine ⟨87425375672249080176249971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58283583781499386784166647 87425375672249080176249971)
        ·
          refine ⟨131138063508373620264374957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87425375672249080176249971 131138063508373620264374957)
          ·
            refine ⟨49176773815640107599140609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131138063508373620264374957 49176773815640107599140609)
            ·
              refine ⟨36882580361730080699355457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49176773815640107599140609 36882580361730080699355457)
              ·
                refine ⟨27661935271297560524516593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36882580361730080699355457 27661935271297560524516593)
                ·
                  refine ⟨20746451453473170393387445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27661935271297560524516593 20746451453473170393387445)
                  ·
                    refine ⟨1944979823763109724380073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20746451453473170393387445 1944979823763109724380073)
                    ·
                      refine ⟨1458734867822332293285055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1944979823763109724380073 1458734867822332293285055)
                      ·
                        rfl

theorem cell23_2840876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 5, 2].length) (baseStart_2840876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840876 prefixEnd_2840876 := by exact prefixLift 2840876
  have htrace : WordTrace (prefixWord ++ tailWord_2840876) baseStart_2840876 baseEnd_2840876 := by
    simpa [prefixWord, tailWord_2840876, baseEnd_2840876] using wordTrace_append hprefix tailTrace_2840876
  have hstable : (prefixWord ++ tailWord_2840876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840876).length < 2 ^ (prefixWord ++ tailWord_2840876).sum := by decide
  have hdescent : baseEnd_2840876 < baseStart_2840876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840963 : List Nat := [1, 1, 1, 3, 6, 1, 2, 2, 6]
def baseStart_2840963 : Nat := 118140960795 + 2840963 * 2 ^ 59
def prefixEnd_2840963 : Nat := 4983230072969 + 3 ^ 40 * 2840963 * 2
def baseEnd_2840963 : Nat := 162086615626585939210795

theorem tailTrace_2840963 : CollatzResearch.WordTrace tailWord_2840963 prefixEnd_2840963 162086615626585939210795 := by
  unfold tailWord_2840963
  simp only [CollatzResearch.WordTrace]
  refine ⟨103618433206683723696935543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69078955471122482464623695 103618433206683723696935543)
  ·
    refine ⟨155427649810025585545403315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103618433206683723696935543 155427649810025585545403315)
    ·
      refine ⟨233141474715038378318104973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155427649810025585545403315 233141474715038378318104973)
      ·
        refine ⟨87428053018139391869289365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233141474715038378318104973 87428053018139391869289365)
        ·
          refine ⟨4098189985225283993872939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87428053018139391869289365 4098189985225283993872939)
          ·
            refine ⟨6147284977837925990809409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4098189985225283993872939 6147284977837925990809409)
            ·
              refine ⟨4610463733378444493107057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6147284977837925990809409 4610463733378444493107057)
              ·
                refine ⟨3457847800033833369830293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4610463733378444493107057 3457847800033833369830293)
                ·
                  refine ⟨162086615626585939210795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3457847800033833369830293 162086615626585939210795)
                  ·
                    rfl

theorem cell23_2840963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 6].length) (baseStart_2840963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840963 prefixEnd_2840963 := by exact prefixLift 2840963
  have htrace : WordTrace (prefixWord ++ tailWord_2840963) baseStart_2840963 baseEnd_2840963 := by
    simpa [prefixWord, tailWord_2840963, baseEnd_2840963] using wordTrace_append hprefix tailTrace_2840963
  have hstable : (prefixWord ++ tailWord_2840963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840963).length < 2 ^ (prefixWord ++ tailWord_2840963).sum := by decide
  have hdescent : baseEnd_2840963 < baseStart_2840963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2840983 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 4, 3, 2]
def baseStart_2840983 : Nat := 118140960795 + 2840983 * 2 ^ 59
def prefixEnd_2840983 : Nat := 4983230072969 + 3 ^ 40 * 2840983 * 2
def baseEnd_2840983 : Nat := 1458789810252363374647063

theorem tailTrace_2840983 : CollatzResearch.WordTrace tailWord_2840983 prefixEnd_2840983 1458789810252363374647063 := by
  unfold tailWord_2840983
  simp only [CollatzResearch.WordTrace]
  refine ⟨103619162666611267112663603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69079441777740844741775735 103619162666611267112663603)
  ·
    refine ⟨155428743999916900668995405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103619162666611267112663603 155428743999916900668995405)
    ·
      refine ⟨58285778999968837750873277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155428743999916900668995405 58285778999968837750873277)
      ·
        refine ⟨21857167124988314156577479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58285778999968837750873277 21857167124988314156577479)
        ·
          refine ⟨32785750687482471234866219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21857167124988314156577479 32785750687482471234866219)
          ·
            refine ⟨49178626031223706852299329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32785750687482471234866219 49178626031223706852299329)
            ·
              refine ⟨36883969523417780139224497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49178626031223706852299329 36883969523417780139224497)
              ·
                refine ⟨27662977142563335104418373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36883969523417780139224497 27662977142563335104418373)
                ·
                  refine ⟨5186808214230625332078445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27662977142563335104418373 5186808214230625332078445)
                  ·
                    refine ⟨1945053080336484499529417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5186808214230625332078445 1945053080336484499529417)
                    ·
                      refine ⟨1458789810252363374647063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1945053080336484499529417 1458789810252363374647063)
                      ·
                        rfl

theorem cell23_2840983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_2840983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2840983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2840983 prefixEnd_2840983 := by exact prefixLift 2840983
  have htrace : WordTrace (prefixWord ++ tailWord_2840983) baseStart_2840983 baseEnd_2840983 := by
    simpa [prefixWord, tailWord_2840983, baseEnd_2840983] using wordTrace_append hprefix tailTrace_2840983
  have hstable : (prefixWord ++ tailWord_2840983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2840983).length < 2 ^ (prefixWord ++ tailWord_2840983).sum := by decide
  have hdescent : baseEnd_2840983 < baseStart_2840983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2840983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841016 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_2841016 : Nat := 118140960795 + 2841016 * 2 ^ 59
def prefixEnd_2841016 : Nat := 4983230072969 + 3 ^ 40 * 2841016 * 2
def baseEnd_2841016 : Nat := 1458806755113961745534411

theorem tailTrace_2841016 : CollatzResearch.WordTrace tailWord_2841016 prefixEnd_2841016 1458806755113961745534411 := by
  unfold tailWord_2841016
  simp only [CollatzResearch.WordTrace]
  refine ⟨51810183137745856874307451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69080244183661142499076601 51810183137745856874307451)
  ·
    refine ⟨77715274706618785311461177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51810183137745856874307451 77715274706618785311461177)
    ·
      refine ⟨58286456029964088983595883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77715274706618785311461177 58286456029964088983595883)
      ·
        refine ⟨87429684044946133475393825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58286456029964088983595883 87429684044946133475393825)
        ·
          refine ⟨65572263033709600106545369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87429684044946133475393825 65572263033709600106545369)
          ·
            refine ⟨49179197275282200079909027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65572263033709600106545369 49179197275282200079909027)
            ·
              refine ⟨73768795912923300119863541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49179197275282200079909027 73768795912923300119863541)
              ·
                refine ⟨6915824616836559386237207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73768795912923300119863541 6915824616836559386237207)
                ·
                  refine ⟨10373736925254839079355811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6915824616836559386237207 10373736925254839079355811)
                  ·
                    refine ⟨15560605387882258619033717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10373736925254839079355811 15560605387882258619033717)
                    ·
                      refine ⟨1458806755113961745534411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15560605387882258619033717 1458806755113961745534411)
                      ·
                        rfl

theorem cell23_2841016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_2841016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841016 prefixEnd_2841016 := by exact prefixLift 2841016
  have htrace : WordTrace (prefixWord ++ tailWord_2841016) baseStart_2841016 baseEnd_2841016 := by
    simpa [prefixWord, tailWord_2841016, baseEnd_2841016] using wordTrace_append hprefix tailTrace_2841016
  have hstable : (prefixWord ++ tailWord_2841016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841016).length < 2 ^ (prefixWord ++ tailWord_2841016).sum := by decide
  have hdescent : baseEnd_2841016 < baseStart_2841016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841050 : List Nat := [3, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3]
def baseStart_2841050 : Nat := 118140960795 + 2841050 * 2 ^ 59
def prefixEnd_2841050 : Nat := 4983230072969 + 3 ^ 40 * 2841050 * 2
def baseEnd_2841050 : Nat := 1458824213456214612509255

theorem tailTrace_2841050 : CollatzResearch.WordTrace tailWord_2841050 prefixEnd_2841050 1458824213456214612509255 := by
  unfold tailWord_2841050
  simp only [CollatzResearch.WordTrace]
  refine ⟨25905401589342134388838151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69081070904912358370235069 25905401589342134388838151)
  ·
    refine ⟨38858102384013201583257227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25905401589342134388838151 38858102384013201583257227)
    ·
      refine ⟨58287153576019802374885841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38858102384013201583257227 58287153576019802374885841)
      ·
        refine ⟨43715365182014851781164381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58287153576019802374885841 43715365182014851781164381)
        ·
          refine ⟨16393261943255569417936643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43715365182014851781164381 16393261943255569417936643)
          ·
            refine ⟨24589892914883354126904965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16393261943255569417936643 24589892914883354126904965)
            ·
              refine ⟨4610604921540628898794681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24589892914883354126904965 4610604921540628898794681)
              ·
                refine ⟨3457953691155471674096011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4610604921540628898794681 3457953691155471674096011)
                ·
                  refine ⟨5186930536733207511144017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457953691155471674096011 5186930536733207511144017)
                  ·
                    refine ⟨3890197902549905633358013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5186930536733207511144017 3890197902549905633358013)
                    ·
                      refine ⟨1458824213456214612509255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3890197902549905633358013 1458824213456214612509255)
                      ·
                        rfl

theorem cell23_2841050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_2841050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841050 prefixEnd_2841050 := by exact prefixLift 2841050
  have htrace : WordTrace (prefixWord ++ tailWord_2841050) baseStart_2841050 baseEnd_2841050 := by
    simpa [prefixWord, tailWord_2841050, baseEnd_2841050] using wordTrace_append hprefix tailTrace_2841050
  have hstable : (prefixWord ++ tailWord_2841050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841050).length < 2 ^ (prefixWord ++ tailWord_2841050).sum := by decide
  have hdescent : baseEnd_2841050 < baseStart_2841050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841058 : List Nat := [3, 3, 3, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_2841058 : Nat := 118140960795 + 2841058 * 2 ^ 59
def prefixEnd_2841058 : Nat := 4983230072969 + 3 ^ 40 * 2841058 * 2
def baseEnd_2841058 : Nat := 1458828321301450581209219

theorem tailTrace_2841058 : CollatzResearch.WordTrace tailWord_2841058 prefixEnd_2841058 1458828321301450581209219 := by
  unfold tailWord_2841058
  simp only [CollatzResearch.WordTrace]
  refine ⟨25905474535334888730410957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69081265427559703281095885 25905474535334888730410957)
  ·
    refine ⟨9714552950750583273904109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25905474535334888730410957 9714552950750583273904109)
    ·
      refine ⟨3642957356531468727714041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9714552950750583273904109 3642957356531468727714041)
      ·
        refine ⟨2732218017398601545785531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3642957356531468727714041 2732218017398601545785531)
        ·
          refine ⟨4098327026097902318678297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2732218017398601545785531 4098327026097902318678297)
          ·
            refine ⟨3073745269573426739008723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4098327026097902318678297 3073745269573426739008723)
            ·
              refine ⟨4610617904360140108513085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3073745269573426739008723 4610617904360140108513085)
              ·
                refine ⟨1728981714135052540692407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4610617904360140108513085 1728981714135052540692407)
                ·
                  refine ⟨2593472571202578811038611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1728981714135052540692407 2593472571202578811038611)
                  ·
                    refine ⟨3890208856803868216557917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2593472571202578811038611 3890208856803868216557917)
                    ·
                      refine ⟨1458828321301450581209219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3890208856803868216557917 1458828321301450581209219)
                      ·
                        rfl

theorem cell23_2841058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_2841058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841058 prefixEnd_2841058 := by exact prefixLift 2841058
  have htrace : WordTrace (prefixWord ++ tailWord_2841058) baseStart_2841058 baseEnd_2841058 := by
    simpa [prefixWord, tailWord_2841058, baseEnd_2841058] using wordTrace_append hprefix tailTrace_2841058
  have hstable : (prefixWord ++ tailWord_2841058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841058).length < 2 ^ (prefixWord ++ tailWord_2841058).sum := by decide
  have hdescent : baseEnd_2841058 < baseStart_2841058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841063 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_2841063 : Nat := 118140960795 + 2841063 * 2 ^ 59
def prefixEnd_2841063 : Nat := 4983230072969 + 3 ^ 40 * 2841063 * 2
def baseEnd_2841063 : Nat := 1458830888704723061646695

theorem tailTrace_2841063 : CollatzResearch.WordTrace tailWord_2841063 prefixEnd_2841063 1458830888704723061646695 := by
  unfold tailWord_2841063
  simp only [CollatzResearch.WordTrace]
  refine ⟨103622080506321440775575843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69081387004214293850383895 103622080506321440775575843)
  ·
    refine ⟨155433120759482161163363765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103622080506321440775575843 155433120759482161163363765)
    ·
      refine ⟨14571855071201452609065353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155433120759482161163363765 14571855071201452609065353)
      ·
        refine ⟨10928891303401089456799015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14571855071201452609065353 10928891303401089456799015)
        ·
          refine ⟨16393336955101634185198523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10928891303401089456799015 16393336955101634185198523)
          ·
            refine ⟨24590005432652451277797785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16393336955101634185198523 24590005432652451277797785)
            ·
              refine ⟨18442504074489338458348339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24590005432652451277797785 18442504074489338458348339)
              ·
                refine ⟨27663756111734007687522509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18442504074489338458348339 27663756111734007687522509)
                ·
                  refine ⟨10373908541900252882820941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27663756111734007687522509 10373908541900252882820941)
                  ·
                    refine ⟨3890215703212594831057853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10373908541900252882820941 3890215703212594831057853)
                    ·
                      refine ⟨1458830888704723061646695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3890215703212594831057853 1458830888704723061646695)
                      ·
                        rfl

theorem cell23_2841063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_2841063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841063 prefixEnd_2841063 := by exact prefixLift 2841063
  have htrace : WordTrace (prefixWord ++ tailWord_2841063) baseStart_2841063 baseEnd_2841063 := by
    simpa [prefixWord, tailWord_2841063, baseEnd_2841063] using wordTrace_append hprefix tailTrace_2841063
  have hstable : (prefixWord ++ tailWord_2841063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841063).length < 2 ^ (prefixWord ++ tailWord_2841063).sum := by decide
  have hdescent : baseEnd_2841063 < baseStart_2841063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841064 : List Nat := [2, 1, 4, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_2841064 : Nat := 118140960795 + 2841064 * 2 ^ 59
def prefixEnd_2841064 : Nat := 4983230072969 + 3 ^ 40 * 2841064 * 2
def baseEnd_2841064 : Nat := 1458831402185377557734191

theorem tailTrace_2841064 : CollatzResearch.WordTrace tailWord_2841064 prefixEnd_2841064 1458831402185377557734191 := by
  unfold tailWord_2841064
  simp only [CollatzResearch.WordTrace]
  refine ⟨51811058489658908973181123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69081411319545211964241497 51811058489658908973181123)
  ·
    refine ⟨77716587734488363459771685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51811058489658908973181123 77716587734488363459771685)
    ·
      refine ⟨14571860200216568148707191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77716587734488363459771685 14571860200216568148707191)
      ·
        refine ⟨21857790300324852223060787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14571860200216568148707191 21857790300324852223060787)
        ·
          refine ⟨32786685450487278334591181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21857790300324852223060787 32786685450487278334591181)
          ·
            refine ⟨12295007043932729375471693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32786685450487278334591181 12295007043932729375471693)
            ·
              refine ⟨4610627641474773515801885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12295007043932729375471693 4610627641474773515801885)
              ·
                refine ⟨1728985365553040068425707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4610627641474773515801885 1728985365553040068425707)
                ·
                  refine ⟨2593478048329560102638561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1728985365553040068425707 2593478048329560102638561)
                  ·
                    refine ⟨1945108536247170076978921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2593478048329560102638561 1945108536247170076978921)
                    ·
                      refine ⟨1458831402185377557734191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1945108536247170076978921 1458831402185377557734191)
                      ·
                        rfl

theorem cell23_2841064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_2841064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841064 prefixEnd_2841064 := by exact prefixLift 2841064
  have htrace : WordTrace (prefixWord ++ tailWord_2841064) baseStart_2841064 baseEnd_2841064 := by
    simpa [prefixWord, tailWord_2841064, baseEnd_2841064] using wordTrace_append hprefix tailTrace_2841064
  have hstable : (prefixWord ++ tailWord_2841064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841064).length < 2 ^ (prefixWord ++ tailWord_2841064).sum := by decide
  have hdescent : baseEnd_2841064 < baseStart_2841064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841080 : List Nat := [2, 1, 2, 1, 1, 4, 2, 4, 2, 1, 3]
def baseStart_2841080 : Nat := 118140960795 + 2841080 * 2 ^ 59
def prefixEnd_2841080 : Nat := 4983230072969 + 3 ^ 40 * 2841080 * 2
def baseEnd_2841080 : Nat := 1458839617875849495134117

theorem tailTrace_2841080 : CollatzResearch.WordTrace tailWord_2841080 prefixEnd_2841080 1458839617875849495134117 := by
  unfold tailWord_2841080
  simp only [CollatzResearch.WordTrace]
  refine ⟨51811350273629926339472347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69081800364839901785963129 51811350273629926339472347)
  ·
    refine ⟨77717025410444889509208521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51811350273629926339472347 77717025410444889509208521)
    ·
      refine ⟨58287769057833667131906391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77717025410444889509208521 58287769057833667131906391)
      ·
        refine ⟨87431653586750500697859587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58287769057833667131906391 87431653586750500697859587)
        ·
          refine ⟨131147480380125751046789381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87431653586750500697859587 131147480380125751046789381)
          ·
            refine ⟨24590152571273578321273009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131147480380125751046789381 24590152571273578321273009)
            ·
              refine ⟨18442614428455183740954757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24590152571273578321273009 18442614428455183740954757)
              ·
                refine ⟨3457990205335346951429017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18442614428455183740954757 3457990205335346951429017)
                ·
                  refine ⟨2593492654001510213571763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3457990205335346951429017 2593492654001510213571763)
                  ·
                    refine ⟨3890238981002265320357645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2593492654001510213571763 3890238981002265320357645)
                    ·
                      refine ⟨1458839617875849495134117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3890238981002265320357645 1458839617875849495134117)
                      ·
                        rfl

theorem cell23_2841080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_2841080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841080 prefixEnd_2841080 := by exact prefixLift 2841080
  have htrace : WordTrace (prefixWord ++ tailWord_2841080) baseStart_2841080 baseEnd_2841080 := by
    simpa [prefixWord, tailWord_2841080, baseEnd_2841080] using wordTrace_append hprefix tailTrace_2841080
  have hstable : (prefixWord ++ tailWord_2841080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841080).length < 2 ^ (prefixWord ++ tailWord_2841080).sum := by decide
  have hdescent : baseEnd_2841080 < baseStart_2841080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841096 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 1, 8]
def baseStart_2841096 : Nat := 118140960795 + 2841096 * 2 ^ 59
def prefixEnd_2841096 : Nat := 4983230072969 + 3 ^ 40 * 2841096 * 2
def baseEnd_2841096 : Nat := 486282611188773810844681

theorem tailTrace_2841096 : CollatzResearch.WordTrace tailWord_2841096 prefixEnd_2841096 486282611188773810844681 := by
  unfold tailWord_2841096
  simp only [CollatzResearch.WordTrace]
  refine ⟨51811642057600943705763571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69082189410134591607684761 51811642057600943705763571)
  ·
    refine ⟨77717463086401415558645357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51811642057600943705763571 77717463086401415558645357)
    ·
      refine ⟨29144048657400530834492009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77717463086401415558645357 29144048657400530834492009)
      ·
        refine ⟨21858036493050398125869007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29144048657400530834492009 21858036493050398125869007)
        ·
          refine ⟨32787054739575597188803511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21858036493050398125869007 32787054739575597188803511)
          ·
            refine ⟨49180582109363395783205267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32787054739575597188803511 49180582109363395783205267)
            ·
              refine ⟨73770873164045093674807901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49180582109363395783205267 73770873164045093674807901)
              ·
                refine ⟨27664077436516910128052963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73770873164045093674807901 27664077436516910128052963)
                ·
                  refine ⟨41496116154775365192079445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27664077436516910128052963 41496116154775365192079445)
                  ·
                    refine ⟨486282611188773810844681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41496116154775365192079445 486282611188773810844681)
                    ·
                      rfl

theorem cell23_2841096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_2841096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841096 prefixEnd_2841096 := by exact prefixLift 2841096
  have htrace : WordTrace (prefixWord ++ tailWord_2841096) baseStart_2841096 baseEnd_2841096 := by
    simpa [prefixWord, tailWord_2841096, baseEnd_2841096] using wordTrace_append hprefix tailTrace_2841096
  have hstable : (prefixWord ++ tailWord_2841096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841096).length < 2 ^ (prefixWord ++ tailWord_2841096).sum := by decide
  have hdescent : baseEnd_2841096 < baseStart_2841096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841101 : List Nat := [1, 7, 1, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2841101 : Nat := 118140960795 + 2841101 * 2 ^ 59
def prefixEnd_2841101 : Nat := 4983230072969 + 3 ^ 40 * 2841101 * 2
def baseEnd_2841101 : Nat := 1458850400969593912971521

theorem tailTrace_2841101 : CollatzResearch.WordTrace tailWord_2841101 prefixEnd_2841101 1458850400969593912971521 := by
  unfold tailWord_2841101
  simp only [CollatzResearch.WordTrace]
  refine ⟨103623466480183773265459157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69082310986789182176972771 103623466480183773265459157)
  ·
    refine ⟨2428674995629307185909199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 103623466480183773265459157 2428674995629307185909199)
    ·
      refine ⟨3643012493443960778863799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2428674995629307185909199 3643012493443960778863799)
      ·
        refine ⟨5464518740165941168295699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3643012493443960778863799 5464518740165941168295699)
        ·
          refine ⟨8196778110248911752443549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5464518740165941168295699 8196778110248911752443549)
          ·
            refine ⟨3073791791343341907166331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8196778110248911752443549 3073791791343341907166331)
            ·
              refine ⟨4610687687015012860749497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3073791791343341907166331 4610687687015012860749497)
              ·
                refine ⟨3458015765261259645562123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4610687687015012860749497 3458015765261259645562123)
                ·
                  refine ⟨5187023647891889468343185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458015765261259645562123 5187023647891889468343185)
                  ·
                    refine ⟨3890267735918917101257389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5187023647891889468343185 3890267735918917101257389)
                    ·
                      refine ⟨1458850400969593912971521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3890267735918917101257389 1458850400969593912971521)
                      ·
                        rfl

theorem cell23_2841101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2841101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841101 prefixEnd_2841101 := by exact prefixLift 2841101
  have htrace : WordTrace (prefixWord ++ tailWord_2841101) baseStart_2841101 baseEnd_2841101 := by
    simpa [prefixWord, tailWord_2841101, baseEnd_2841101] using wordTrace_append hprefix tailTrace_2841101
  have hstable : (prefixWord ++ tailWord_2841101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841101).length < 2 ^ (prefixWord ++ tailWord_2841101).sum := by decide
  have hdescent : baseEnd_2841101 < baseStart_2841101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841123 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 5]
def baseStart_2841123 : Nat := 118140960795 + 2841123 * 2 ^ 59
def prefixEnd_2841123 : Nat := 4983230072969 + 3 ^ 40 * 2841123 * 2
def baseEnd_2841123 : Nat := 1458861697543992826896419

theorem tailTrace_2841123 : CollatzResearch.WordTrace tailWord_2841123 prefixEnd_2841123 1458861697543992826896419 := by
  unfold tailWord_2841123
  simp only [CollatzResearch.WordTrace]
  refine ⟨103624268886104071022760023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69082845924069380681840015 103624268886104071022760023)
  ·
    refine ⟨155436403329156106534140035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103624268886104071022760023 155436403329156106534140035)
    ·
      refine ⟨233154604993734159801210053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155436403329156106534140035 233154604993734159801210053)
      ·
        refine ⟨43716488436325154962726885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233154604993734159801210053 43716488436325154962726885)
        ·
          refine ⟨8196841581810966555511291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43716488436325154962726885 8196841581810966555511291)
          ·
            refine ⟨12295262372716449833266937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8196841581810966555511291 12295262372716449833266937)
            ·
              refine ⟨9221446779537337374950203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12295262372716449833266937 9221446779537337374950203)
              ·
                refine ⟨13832170169306006062425305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9221446779537337374950203 13832170169306006062425305)
                ·
                  refine ⟨10374127626979504546818979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13832170169306006062425305 10374127626979504546818979)
                  ·
                    refine ⟨15561191440469256820228469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10374127626979504546818979 15561191440469256820228469)
                    ·
                      refine ⟨1458861697543992826896419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15561191440469256820228469 1458861697543992826896419)
                      ·
                        rfl

theorem cell23_2841123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_2841123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841123 prefixEnd_2841123 := by exact prefixLift 2841123
  have htrace : WordTrace (prefixWord ++ tailWord_2841123) baseStart_2841123 baseEnd_2841123 := by
    simpa [prefixWord, tailWord_2841123, baseEnd_2841123] using wordTrace_append hprefix tailTrace_2841123
  have hstable : (prefixWord ++ tailWord_2841123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841123).length < 2 ^ (prefixWord ++ tailWord_2841123).sum := by decide
  have hdescent : baseEnd_2841123 < baseStart_2841123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841136 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 7]
def baseStart_2841136 : Nat := 118140960795 + 2841136 * 2 ^ 59
def prefixEnd_2841136 : Nat := 4983230072969 + 3 ^ 40 * 2841136 * 2
def baseEnd_2841136 : Nat := 1458868372792501276033859

theorem tailTrace_2841136 : CollatzResearch.WordTrace tailWord_2841136 prefixEnd_2841136 1458868372792501276033859 := by
  unfold tailWord_2841136
  simp only [CollatzResearch.WordTrace]
  refine ⟨51812371517528487121491631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69083162023371316161988841 51812371517528487121491631)
  ·
    refine ⟨77718557276292730682237447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51812371517528487121491631 77718557276292730682237447)
    ·
      refine ⟨116577835914439096023356171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77718557276292730682237447 116577835914439096023356171)
      ·
        refine ⟨174866753871658644035034257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116577835914439096023356171 174866753871658644035034257)
        ·
          refine ⟨131150065403743983026275693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174866753871658644035034257 131150065403743983026275693)
          ·
            refine ⟨49181274526403993634853385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131150065403743983026275693 49181274526403993634853385)
            ·
              refine ⟨36885955894802995226140039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49181274526403993634853385 36885955894802995226140039)
              ·
                refine ⟨55328933842204492839210059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36885955894802995226140039 55328933842204492839210059)
                ·
                  refine ⟨82993400763306739258815089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55328933842204492839210059 82993400763306739258815089)
                  ·
                    refine ⟨62245050572480054444111317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82993400763306739258815089 62245050572480054444111317)
                    ·
                      refine ⟨1458868372792501276033859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62245050572480054444111317 1458868372792501276033859)
                      ·
                        rfl

theorem cell23_2841136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_2841136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841136 prefixEnd_2841136 := by exact prefixLift 2841136
  have htrace : WordTrace (prefixWord ++ tailWord_2841136) baseStart_2841136 baseEnd_2841136 := by
    simpa [prefixWord, tailWord_2841136, baseEnd_2841136] using wordTrace_append hprefix tailTrace_2841136
  have hstable : (prefixWord ++ tailWord_2841136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841136).length < 2 ^ (prefixWord ++ tailWord_2841136).sum := by decide
  have hdescent : baseEnd_2841136 < baseStart_2841136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841137 : List Nat := [1, 2, 2, 3, 1, 1, 3, 4, 2, 2, 2]
def baseStart_2841137 : Nat := 118140960795 + 2841137 * 2 ^ 59
def prefixEnd_2841137 : Nat := 4983230072969 + 3 ^ 40 * 2841137 * 2
def baseEnd_2841137 : Nat := 1458868886273155772121355

theorem tailTrace_2841137 : CollatzResearch.WordTrace tailWord_2841137 prefixEnd_2841137 1458868886273155772121355 := by
  unfold tailWord_2841137
  simp only [CollatzResearch.WordTrace]
  refine ⟨103624779508053351413769665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69083186338702234275846443 103624779508053351413769665)
  ·
    refine ⟨77718584631040013560327249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103624779508053351413769665 77718584631040013560327249)
    ·
      refine ⟨58288938473280010170245437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77718584631040013560327249 58288938473280010170245437)
      ·
        refine ⟨21858351927480003813842039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58288938473280010170245437 21858351927480003813842039)
        ·
          refine ⟨32787527891220005720763059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21858351927480003813842039 32787527891220005720763059)
          ·
            refine ⟨49181291836830008581144589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32787527891220005720763059 49181291836830008581144589)
            ·
              refine ⟨18442984438811253217929221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49181291836830008581144589 18442984438811253217929221)
              ·
                refine ⟨3458059582277109978361729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18442984438811253217929221 3458059582277109978361729)
                ·
                  refine ⟨2593544686707832483771297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3458059582277109978361729 2593544686707832483771297)
                  ·
                    refine ⟨1945158515030874362828473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2593544686707832483771297 1945158515030874362828473)
                    ·
                      refine ⟨1458868886273155772121355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1945158515030874362828473 1458868886273155772121355)
                      ·
                        rfl

theorem cell23_2841137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_2841137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841137 prefixEnd_2841137 := by exact prefixLift 2841137
  have htrace : WordTrace (prefixWord ++ tailWord_2841137) baseStart_2841137 baseEnd_2841137 := by
    simpa [prefixWord, tailWord_2841137, baseEnd_2841137] using wordTrace_append hprefix tailTrace_2841137
  have hstable : (prefixWord ++ tailWord_2841137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841137).length < 2 ^ (prefixWord ++ tailWord_2841137).sum := by decide
  have hdescent : baseEnd_2841137 < baseStart_2841137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841193 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 4, 1, 4]
def baseStart_2841193 : Nat := 118140960795 + 2841193 * 2 ^ 59
def prefixEnd_2841193 : Nat := 4983230072969 + 3 ^ 40 * 2841193 * 2
def baseEnd_2841193 : Nat := 1458897641189807553021097

theorem tailTrace_2841193 : CollatzResearch.WordTrace tailWord_2841193 prefixEnd_2841193 1458897641189807553021097 := by
  unfold tailWord_2841193
  simp only [CollatzResearch.WordTrace]
  refine ⟨103626821995850472977808233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69084547997233648651872155 103626821995850472977808233)
  ·
    refine ⟨77720116496887854733356175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103626821995850472977808233 77720116496887854733356175)
    ·
      refine ⟨116580174745331782100034263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77720116496887854733356175 116580174745331782100034263)
      ·
        refine ⟨174870262117997673150051395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116580174745331782100034263 174870262117997673150051395)
        ·
          refine ⟨262305393176996509725077093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174870262117997673150051395 262305393176996509725077093)
          ·
            refine ⟨49182261220686845573451955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262305393176996509725077093 49182261220686845573451955)
            ·
              refine ⟨73773391831030268360177933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49182261220686845573451955 73773391831030268360177933)
              ·
                refine ⟨27665021936636350635066725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73773391831030268360177933 27665021936636350635066725)
                ·
                  refine ⟨5187191613119315744075011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27665021936636350635066725 5187191613119315744075011)
                  ·
                    refine ⟨7780787419678973616112517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5187191613119315744075011 7780787419678973616112517)
                    ·
                      refine ⟨1458897641189807553021097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7780787419678973616112517 1458897641189807553021097)
                      ·
                        rfl

theorem cell23_2841193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_2841193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841193 prefixEnd_2841193 := by exact prefixLift 2841193
  have htrace : WordTrace (prefixWord ++ tailWord_2841193) baseStart_2841193 baseEnd_2841193 := by
    simpa [prefixWord, tailWord_2841193, baseEnd_2841193] using wordTrace_append hprefix tailTrace_2841193
  have hstable : (prefixWord ++ tailWord_2841193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841193).length < 2 ^ (prefixWord ++ tailWord_2841193).sum := by decide
  have hdescent : baseEnd_2841193 < baseStart_2841193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841223 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_2841223 : Nat := 118140960795 + 2841223 * 2 ^ 59
def prefixEnd_2841223 : Nat := 4983230072969 + 3 ^ 40 * 2841223 * 2
def baseEnd_2841223 : Nat := 1458913045609442435645959

theorem tailTrace_2841223 : CollatzResearch.WordTrace tailWord_2841223 prefixEnd_2841223 1458913045609442435645959 := by
  unfold tailWord_2841223
  simp only [CollatzResearch.WordTrace]
  refine ⟨103627916185741788101400323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69085277457161192067600215 103627916185741788101400323)
  ·
    refine ⟨155441874278612682152100485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103627916185741788101400323 155441874278612682152100485)
    ·
      refine ⟨29145351427239877903518841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155441874278612682152100485 29145351427239877903518841)
      ·
        refine ⟨21859013570429908427639131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29145351427239877903518841 21859013570429908427639131)
        ·
          refine ⟨32788520355644862641458697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21859013570429908427639131 32788520355644862641458697)
          ·
            refine ⟨24591390266733646981094023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32788520355644862641458697 24591390266733646981094023)
            ·
              refine ⟨36887085400100470471641035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24591390266733646981094023 36887085400100470471641035)
              ·
                refine ⟨55330628100150705707461553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36887085400100470471641035 55330628100150705707461553)
                ·
                  refine ⟨41497971075113029280596165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55330628100150705707461553 41497971075113029280596165)
                  ·
                    refine ⟨7780869576583692990111781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41497971075113029280596165 7780869576583692990111781)
                    ·
                      refine ⟨1458913045609442435645959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7780869576583692990111781 1458913045609442435645959)
                      ·
                        rfl

theorem cell23_2841223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_2841223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841223 prefixEnd_2841223 := by exact prefixLift 2841223
  have htrace : WordTrace (prefixWord ++ tailWord_2841223) baseStart_2841223 baseEnd_2841223 := by
    simpa [prefixWord, tailWord_2841223, baseEnd_2841223] using wordTrace_append hprefix tailTrace_2841223
  have hstable : (prefixWord ++ tailWord_2841223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841223).length < 2 ^ (prefixWord ++ tailWord_2841223).sum := by decide
  have hdescent : baseEnd_2841223 < baseStart_2841223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841230 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2841230 : Nat := 118140960795 + 2841230 * 2 ^ 59
def prefixEnd_2841230 : Nat := 4983230072969 + 3 ^ 40 * 2841230 * 2
def baseEnd_2841230 : Nat := 1458916639974023908258427

theorem tailTrace_2841230 : CollatzResearch.WordTrace tailWord_2841230 prefixEnd_2841230 1458916639974023908258427 := by
  unfold tailWord_2841230
  simp only [CollatzResearch.WordTrace]
  refine ⟨12953521437089553537113143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69085447664477618864603429 12953521437089553537113143)
  ·
    refine ⟨19430282155634330305669715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12953521437089553537113143 19430282155634330305669715)
    ·
      refine ⟨29145423233451495458504573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19430282155634330305669715 29145423233451495458504573)
      ·
        refine ⟨10929533712544310796939215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29145423233451495458504573 10929533712544310796939215)
        ·
          refine ⟨16394300568816466195408823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10929533712544310796939215 16394300568816466195408823)
          ·
            refine ⟨24591450853224699293113235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16394300568816466195408823 24591450853224699293113235)
            ·
              refine ⟨36887176279837048939669853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24591450853224699293113235 36887176279837048939669853)
              ·
                refine ⟨13832691104938893352376195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36887176279837048939669853 13832691104938893352376195)
                ·
                  refine ⟨20749036657408340028564293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13832691104938893352376195 20749036657408340028564293)
                  ·
                    refine ⟨3890444373264063755355805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20749036657408340028564293 3890444373264063755355805)
                    ·
                      refine ⟨1458916639974023908258427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3890444373264063755355805 1458916639974023908258427)
                      ·
                        rfl

theorem cell23_2841230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2841230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841230 prefixEnd_2841230 := by exact prefixLift 2841230
  have htrace : WordTrace (prefixWord ++ tailWord_2841230) baseStart_2841230 baseEnd_2841230 := by
    simpa [prefixWord, tailWord_2841230, baseEnd_2841230] using wordTrace_append hprefix tailTrace_2841230
  have hstable : (prefixWord ++ tailWord_2841230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841230).length < 2 ^ (prefixWord ++ tailWord_2841230).sum := by decide
  have hdescent : baseEnd_2841230 < baseStart_2841230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841267 : List Nat := [1, 1, 1, 2, 3, 6, 2, 1, 6]
def baseStart_2841267 : Nat := 118140960795 + 2841267 * 2 ^ 59
def prefixEnd_2841267 : Nat := 4983230072969 + 3 ^ 40 * 2841267 * 2
def baseEnd_2841267 : Nat := 162103959862026695943973

theorem tailTrace_2841267 : CollatzResearch.WordTrace tailWord_2841267 prefixEnd_2841267 162103959862026695943973 := by
  unfold tailWord_2841267
  simp only [CollatzResearch.WordTrace]
  refine ⟨103629520997582383616002055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69086347331721589077334703 103629520997582383616002055)
  ·
    refine ⟨155444281496373575424003083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103629520997582383616002055 155444281496373575424003083)
    ·
      refine ⟨233166422244560363136004625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155444281496373575424003083 233166422244560363136004625)
      ·
        refine ⟨174874816683420272352003469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233166422244560363136004625 174874816683420272352003469)
        ·
          refine ⟨65578056256282602132001301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174874816683420272352003469 65578056256282602132001301)
          ·
            refine ⟨3073971387013246974937561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65578056256282602132001301 3073971387013246974937561)
            ·
              refine ⟨2305478540259935231203171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3073971387013246974937561 2305478540259935231203171)
              ·
                refine ⟨3458217810389902846804757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2305478540259935231203171 3458217810389902846804757)
                ·
                  refine ⟨162103959862026695943973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3458217810389902846804757 162103959862026695943973)
                  ·
                    rfl

theorem cell23_2841267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 6].length) (baseStart_2841267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841267 prefixEnd_2841267 := by exact prefixLift 2841267
  have htrace : WordTrace (prefixWord ++ tailWord_2841267) baseStart_2841267 baseEnd_2841267 := by
    simpa [prefixWord, tailWord_2841267, baseEnd_2841267] using wordTrace_append hprefix tailTrace_2841267
  have hstable : (prefixWord ++ tailWord_2841267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841267).length < 2 ^ (prefixWord ++ tailWord_2841267).sum := by decide
  have hdescent : baseEnd_2841267 < baseStart_2841267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841280 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 3, 5]
def baseStart_2841280 : Nat := 118140960795 + 2841280 * 2 ^ 59
def prefixEnd_2841280 : Nat := 4983230072969 + 3 ^ 40 * 2841280 * 2
def baseEnd_2841280 : Nat := 486314104668916237544399

theorem tailTrace_2841280 : CollatzResearch.WordTrace tailWord_2841280 prefixEnd_2841280 486314104668916237544399 := by
  unfold tailWord_2841280
  simp only [CollatzResearch.WordTrace]
  refine ⟨51814997573267643418112647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69086663431023524557483529 51814997573267643418112647)
  ·
    refine ⟨77722496359901465127168971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51814997573267643418112647 77722496359901465127168971)
    ·
      refine ⟨116583744539852197690753457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77722496359901465127168971 116583744539852197690753457)
      ·
        refine ⟨87437808404889148268065093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116583744539852197690753457 87437808404889148268065093)
        ·
          refine ⟨16394589075916715300262205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87437808404889148268065093 16394589075916715300262205)
          ·
            refine ⟨6147970903468768237598327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16394589075916715300262205 6147970903468768237598327)
            ·
              refine ⟨9221956355203152356397491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6147970903468768237598327 9221956355203152356397491)
              ·
                refine ⟨13832934532804728534596237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9221956355203152356397491 13832934532804728534596237)
                ·
                  refine ⟨5187350449801773200473589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13832934532804728534596237 5187350449801773200473589)
                  ·
                    refine ⟨486314104668916237544399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5187350449801773200473589 486314104668916237544399)
                    ·
                      rfl

theorem cell23_2841280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3, 5].length) (baseStart_2841280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841280 prefixEnd_2841280 := by exact prefixLift 2841280
  have htrace : WordTrace (prefixWord ++ tailWord_2841280) baseStart_2841280 baseEnd_2841280 := by
    simpa [prefixWord, tailWord_2841280, baseEnd_2841280] using wordTrace_append hprefix tailTrace_2841280
  have hstable : (prefixWord ++ tailWord_2841280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841280).length < 2 ^ (prefixWord ++ tailWord_2841280).sum := by decide
  have hdescent : baseEnd_2841280 < baseStart_2841280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841281 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2841281 : Nat := 118140960795 + 2841281 * 2 ^ 59
def prefixEnd_2841281 : Nat := 4983230072969 + 3 ^ 40 * 2841281 * 2
def baseEnd_2841281 : Nat := 1458942827487403208720693

theorem tailTrace_2841281 : CollatzResearch.WordTrace tailWord_2841281 prefixEnd_2841281 1458942827487403208720693 := by
  unfold tailWord_2841281
  simp only [CollatzResearch.WordTrace]
  refine ⟨103630031619531664007011697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69086687746354442671341131 103630031619531664007011697)
  ·
    refine ⟨77722523714648748005258773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103630031619531664007011697 77722523714648748005258773)
    ·
      refine ⟨3643243299124160062746505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77722523714648748005258773 3643243299124160062746505)
      ·
        refine ⟨2732432474343120047059879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3643243299124160062746505 2732432474343120047059879)
        ·
          refine ⟨4098648711514680070589819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2732432474343120047059879 4098648711514680070589819)
          ·
            refine ⟨6147973067272020105884729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4098648711514680070589819 6147973067272020105884729)
            ·
              refine ⟨4610979800454015079413547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6147973067272020105884729 4610979800454015079413547)
              ·
                refine ⟨6916469700681022619120321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4610979800454015079413547 6916469700681022619120321)
                ·
                  refine ⟨5187352275510766964340241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6916469700681022619120321 5187352275510766964340241)
                  ·
                    refine ⟨3890514206633075223255181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5187352275510766964340241 3890514206633075223255181)
                    ·
                      refine ⟨1458942827487403208720693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3890514206633075223255181 1458942827487403208720693)
                      ·
                        rfl

theorem cell23_2841281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2841281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841281 prefixEnd_2841281 := by exact prefixLift 2841281
  have htrace : WordTrace (prefixWord ++ tailWord_2841281) baseStart_2841281 baseEnd_2841281 := by
    simpa [prefixWord, tailWord_2841281, baseEnd_2841281] using wordTrace_append hprefix tailTrace_2841281
  have hstable : (prefixWord ++ tailWord_2841281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841281).length < 2 ^ (prefixWord ++ tailWord_2841281).sum := by decide
  have hdescent : baseEnd_2841281 < baseStart_2841281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841297 : List Nat := [1, 2, 2, 1, 2, 3, 5, 1, 1, 5]
def baseStart_2841297 : Nat := 118140960795 + 2841297 * 2 ^ 59
def prefixEnd_2841297 : Nat := 4983230072969 + 3 ^ 40 * 2841297 * 2
def baseEnd_2841297 : Nat := 486317014392625048706873

theorem tailTrace_2841297 : CollatzResearch.WordTrace tailWord_2841297 prefixEnd_2841297 486317014392625048706873 := by
  unfold tailWord_2841297
  simp only [CollatzResearch.WordTrace]
  refine ⟨103630615187473698739594145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69087076791649132493062763 103630615187473698739594145)
  ·
    refine ⟨77722961390605274054695609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103630615187473698739594145 77722961390605274054695609)
    ·
      refine ⟨58292221042953955541021707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77722961390605274054695609 58292221042953955541021707)
      ·
        refine ⟨87438331564430933311532561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58292221042953955541021707 87438331564430933311532561)
        ·
          refine ⟨65578748673323199983649421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87438331564430933311532561 65578748673323199983649421)
          ·
            refine ⟨24592030752496199993868533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65578748673323199983649421 24592030752496199993868533)
            ·
              refine ⟨2305502883046518749425175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24592030752496199993868533 2305502883046518749425175)
              ·
                refine ⟨3458254324569778124137763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2305502883046518749425175 3458254324569778124137763)
                ·
                  refine ⟨5187381486854667186206645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458254324569778124137763 5187381486854667186206645)
                  ·
                    refine ⟨486317014392625048706873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5187381486854667186206645 486317014392625048706873)
                    ·
                      rfl

theorem cell23_2841297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_2841297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841297 prefixEnd_2841297 := by exact prefixLift 2841297
  have htrace : WordTrace (prefixWord ++ tailWord_2841297) baseStart_2841297 baseEnd_2841297 := by
    simpa [prefixWord, tailWord_2841297, baseEnd_2841297] using wordTrace_append hprefix tailTrace_2841297
  have hstable : (prefixWord ++ tailWord_2841297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841297).length < 2 ^ (prefixWord ++ tailWord_2841297).sum := by decide
  have hdescent : baseEnd_2841297 < baseStart_2841297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841311 : List Nat := [1, 1, 2, 3, 2, 3, 4, 2, 1, 1, 3]
def baseStart_2841311 : Nat := 118140960795 + 2841311 * 2 ^ 59
def prefixEnd_2841311 : Nat := 4983230072969 + 3 ^ 40 * 2841311 * 2
def baseEnd_2841311 : Nat := 1458958231907038091345555

theorem tailTrace_2841311 : CollatzResearch.WordTrace tailWord_2841311 prefixEnd_2841311 1458958231907038091345555 := by
  unfold tailWord_2841311
  simp only [CollatzResearch.WordTrace]
  refine ⟨103631125809422979130603787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69087417206281986087069191 103631125809422979130603787)
  ·
    refine ⟨155446688714134468695905681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103631125809422979130603787 155446688714134468695905681)
    ·
      refine ⟨116585016535600851521929261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155446688714134468695905681 116585016535600851521929261)
      ·
        refine ⟨43719381200850319320723473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116585016535600851521929261 43719381200850319320723473)
        ·
          refine ⟨32789535900637739490542605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43719381200850319320723473 32789535900637739490542605)
          ·
            refine ⟨12296075962739152308953477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32789535900637739490542605 12296075962739152308953477)
            ·
              refine ⟨2305514243013591057928777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12296075962739152308953477 2305514243013591057928777)
              ·
                refine ⟨1729135682260193293446583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2305514243013591057928777 1729135682260193293446583)
                ·
                  refine ⟨2593703523390289940169875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1729135682260193293446583 2593703523390289940169875)
                  ·
                    refine ⟨3890555285085434910254813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2593703523390289940169875 3890555285085434910254813)
                    ·
                      refine ⟨1458958231907038091345555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3890555285085434910254813 1458958231907038091345555)
                      ·
                        rfl

theorem cell23_2841311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_2841311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841311 prefixEnd_2841311 := by exact prefixLift 2841311
  have htrace : WordTrace (prefixWord ++ tailWord_2841311) baseStart_2841311 baseEnd_2841311 := by
    simpa [prefixWord, tailWord_2841311, baseEnd_2841311] using wordTrace_append hprefix tailTrace_2841311
  have hstable : (prefixWord ++ tailWord_2841311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841311).length < 2 ^ (prefixWord ++ tailWord_2841311).sum := by decide
  have hdescent : baseEnd_2841311 < baseStart_2841311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841327 : List Nat := [1, 1, 2, 1, 5, 2, 2, 3, 2, 4]
def baseStart_2841327 : Nat := 118140960795 + 2841327 * 2 ^ 59
def prefixEnd_2841327 : Nat := 4983230072969 + 3 ^ 40 * 2841327 * 2
def baseEnd_2841327 : Nat := 486322149199170009581827

theorem tailTrace_2841327 : CollatzResearch.WordTrace tailWord_2841327 prefixEnd_2841327 486322149199170009581827 := by
  unfold tailWord_2841327
  simp only [CollatzResearch.WordTrace]
  refine ⟨103631709377365013863186235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69087806251576675908790823 103631709377365013863186235)
  ·
    refine ⟨155447564066047520794779353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103631709377365013863186235 155447564066047520794779353)
    ·
      refine ⟨116585673049535640596084515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155447564066047520794779353 116585673049535640596084515)
      ·
        refine ⟨174878509574303460894126773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116585673049535640596084515 174878509574303460894126773)
        ·
          refine ⟨16394860272590949458824385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174878509574303460894126773 16394860272590949458824385)
          ·
            refine ⟨12296145204443212094118289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16394860272590949458824385 12296145204443212094118289)
            ·
              refine ⟨9222108903332409070588717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12296145204443212094118289 9222108903332409070588717)
              ·
                refine ⟨3458290838749653401470769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9222108903332409070588717 3458290838749653401470769)
                ·
                  refine ⟨2593718129062240051103077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3458290838749653401470769 2593718129062240051103077)
                  ·
                    refine ⟨486322149199170009581827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2593718129062240051103077 486322149199170009581827)
                    ·
                      rfl

theorem cell23_2841327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 4].length) (baseStart_2841327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841327 prefixEnd_2841327 := by exact prefixLift 2841327
  have htrace : WordTrace (prefixWord ++ tailWord_2841327) baseStart_2841327 baseEnd_2841327 := by
    simpa [prefixWord, tailWord_2841327, baseEnd_2841327] using wordTrace_append hprefix tailTrace_2841327
  have hstable : (prefixWord ++ tailWord_2841327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841327).length < 2 ^ (prefixWord ++ tailWord_2841327).sum := by decide
  have hdescent : baseEnd_2841327 < baseStart_2841327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841351 : List Nat := [1, 1, 4, 4, 1, 3, 2, 1, 1, 1, 4]
def baseStart_2841351 : Nat := 118140960795 + 2841351 * 2 ^ 59
def prefixEnd_2841351 : Nat := 4983230072969 + 3 ^ 40 * 2841351 * 2
def baseEnd_2841351 : Nat := 1458978771133217934845371

theorem tailTrace_2841351 : CollatzResearch.WordTrace tailWord_2841351 prefixEnd_2841351 1458978771133217934845371 := by
  unfold tailWord_2841351
  simp only [CollatzResearch.WordTrace]
  refine ⟨103632584729278065962059907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69088389819518710641373271 103632584729278065962059907)
  ·
    refine ⟨155448877093917098943089861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103632584729278065962059907 155448877093917098943089861)
    ·
      refine ⟨29146664455109456051829349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155448877093917098943089861 29146664455109456051829349)
      ·
        refine ⟨5464999585333023009718003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29146664455109456051829349 5464999585333023009718003)
        ·
          refine ⟨8197499377999534514577005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5464999585333023009718003 8197499377999534514577005)
          ·
            refine ⟨3074062266749825442966377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8197499377999534514577005 3074062266749825442966377)
            ·
              refine ⟨2305546700062369082224783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3074062266749825442966377 2305546700062369082224783)
              ·
                refine ⟨3458320050093553623337175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2305546700062369082224783 3458320050093553623337175)
                ·
                  refine ⟨5187480075140330435005763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458320050093553623337175 5187480075140330435005763)
                  ·
                    refine ⟨7781220112710495652508645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5187480075140330435005763 7781220112710495652508645)
                    ·
                      refine ⟨1458978771133217934845371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7781220112710495652508645 1458978771133217934845371)
                      ·
                        rfl

theorem cell23_2841351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_2841351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841351 prefixEnd_2841351 := by exact prefixLift 2841351
  have htrace : WordTrace (prefixWord ++ tailWord_2841351) baseStart_2841351 baseEnd_2841351 := by
    simpa [prefixWord, tailWord_2841351, baseEnd_2841351] using wordTrace_append hprefix tailTrace_2841351
  have hstable : (prefixWord ++ tailWord_2841351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841351).length < 2 ^ (prefixWord ++ tailWord_2841351).sum := by decide
  have hdescent : baseEnd_2841351 < baseStart_2841351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841424 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 4, 2, 2]
def baseStart_2841424 : Nat := 118140960795 + 2841424 * 2 ^ 59
def prefixEnd_2841424 : Nat := 4983230072969 + 3 ^ 40 * 2841424 * 2
def baseEnd_2841424 : Nat := 1459016255220996149232535

theorem tailTrace_2841424 : CollatzResearch.WordTrace tailWord_2841424 prefixEnd_2841424 1459016255220996149232535 := by
  unfold tailWord_2841424
  simp only [CollatzResearch.WordTrace]
  refine ⟨51817623629006799714733663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69090164838675732952978217 51817623629006799714733663)
  ·
    refine ⟨77726435443510199572100495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51817623629006799714733663 77726435443510199572100495)
    ·
      refine ⟨116589653165265299358150743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77726435443510199572100495 116589653165265299358150743)
      ·
        refine ⟨174884479747897949037226115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116589653165265299358150743 174884479747897949037226115)
        ·
          refine ⟨262326719621846923555839173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174884479747897949037226115 262326719621846923555839173)
          ·
            refine ⟨49186259929096298166719845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262326719621846923555839173 49186259929096298166719845)
            ·
              refine ⟨9222423736705555906259971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49186259929096298166719845 9222423736705555906259971)
              ·
                refine ⟨13833635605058333859389957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9222423736705555906259971 13833635605058333859389957)
                ·
                  refine ⟨2593806675948437598635617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13833635605058333859389957 2593806675948437598635617)
                  ·
                    refine ⟨1945355006961328198976713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2593806675948437598635617 1945355006961328198976713)
                    ·
                      refine ⟨1459016255220996149232535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1945355006961328198976713 1459016255220996149232535)
                      ·
                        rfl

theorem cell23_2841424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 4, 2, 2].length) (baseStart_2841424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841424 prefixEnd_2841424 := by exact prefixLift 2841424
  have htrace : WordTrace (prefixWord ++ tailWord_2841424) baseStart_2841424 baseEnd_2841424 := by
    simpa [prefixWord, tailWord_2841424, baseEnd_2841424] using wordTrace_append hprefix tailTrace_2841424
  have hstable : (prefixWord ++ tailWord_2841424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841424).length < 2 ^ (prefixWord ++ tailWord_2841424).sum := by decide
  have hdescent : baseEnd_2841424 < baseStart_2841424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841477 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 2, 5]
def baseStart_2841477 : Nat := 118140960795 + 2841477 * 2 ^ 59
def prefixEnd_2841477 : Nat := 4983230072969 + 3 ^ 40 * 2841477 * 2
def baseEnd_2841477 : Nat := 486347823231894813956597

theorem tailTrace_2841477 : CollatzResearch.WordTrace tailWord_2841477 prefixEnd_2841477 486347823231894813956597 := by
  unfold tailWord_2841477
  simp only [CollatzResearch.WordTrace]
  refine ⟨103637180326821589481146685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69091453551214392987431123 103637180326821589481146685)
  ·
    refine ⟨38863942622558096055430007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103637180326821589481146685 38863942622558096055430007)
    ·
      refine ⟨58295913933837144083145011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38863942622558096055430007 58295913933837144083145011)
      ·
        refine ⟨87443870900755716124717517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58295913933837144083145011 87443870900755716124717517)
        ·
          refine ⟨32791451587783393546769069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87443870900755716124717517 32791451587783393546769069)
          ·
            refine ⟨12296794345418772580038401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32791451587783393546769069 12296794345418772580038401)
            ·
              refine ⟨9222595759064079435028801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12296794345418772580038401 9222595759064079435028801)
              ·
                refine ⟨6916946819298059576271601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9222595759064079435028801 6916946819298059576271601)
                ·
                  refine ⟨5187710114473544682203701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6916946819298059576271601 5187710114473544682203701)
                  ·
                    refine ⟨486347823231894813956597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5187710114473544682203701 486347823231894813956597)
                    ·
                      rfl

theorem cell23_2841477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_2841477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841477 prefixEnd_2841477 := by exact prefixLift 2841477
  have htrace : WordTrace (prefixWord ++ tailWord_2841477) baseStart_2841477 baseEnd_2841477 := by
    simpa [prefixWord, tailWord_2841477, baseEnd_2841477] using wordTrace_append hprefix tailTrace_2841477
  have hstable : (prefixWord ++ tailWord_2841477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841477).length < 2 ^ (prefixWord ++ tailWord_2841477).sum := by decide
  have hdescent : baseEnd_2841477 < baseStart_2841477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841481 : List Nat := [1, 2, 1, 1, 5, 4, 2, 2, 5]
def baseStart_2841481 : Nat := 118140960795 + 2841481 * 2 ^ 59
def prefixEnd_2841481 : Nat := 4983230072969 + 3 ^ 40 * 2841481 * 2
def baseEnd_2841481 : Nat := 162116169290922491802197

theorem tailTrace_2841481 : CollatzResearch.WordTrace tailWord_2841481 prefixEnd_2841481 162116169290922491802197 := by
  unfold tailWord_2841481
  simp only [CollatzResearch.WordTrace]
  refine ⟨103637326218807098164292297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69091550812538065442861531 103637326218807098164292297)
  ·
    refine ⟨77727994664105323623219223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103637326218807098164292297 77727994664105323623219223)
    ·
      refine ⟨116591991996157985434828835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77727994664105323623219223 116591991996157985434828835)
      ·
        refine ⟨174887987994236978152243253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116591991996157985434828835 174887987994236978152243253)
        ·
          refine ⟨16395748874459716701772805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174887987994236978152243253 16395748874459716701772805)
          ·
            refine ⟨3074202913961196881582401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16395748874459716701772805 3074202913961196881582401)
            ·
              refine ⟨2305652185470897661186801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3074202913961196881582401 2305652185470897661186801)
              ·
                refine ⟨1729239139103173245890101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2305652185470897661186801 1729239139103173245890101)
                ·
                  refine ⟨162116169290922491802197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1729239139103173245890101 162116169290922491802197)
                  ·
                    rfl

theorem cell23_2841481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 5].length) (baseStart_2841481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841481 prefixEnd_2841481 := by exact prefixLift 2841481
  have htrace : WordTrace (prefixWord ++ tailWord_2841481) baseStart_2841481 baseEnd_2841481 := by
    simpa [prefixWord, tailWord_2841481, baseEnd_2841481] using wordTrace_append hprefix tailTrace_2841481
  have hstable : (prefixWord ++ tailWord_2841481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841481).length < 2 ^ (prefixWord ++ tailWord_2841481).sum := by decide
  have hdescent : baseEnd_2841481 < baseStart_2841481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841507 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 5, 4]
def baseStart_2841507 : Nat := 118140960795 + 2841507 * 2 ^ 59
def prefixEnd_2841507 : Nat := 4983230072969 + 3 ^ 40 * 2841507 * 2
def baseEnd_2841507 : Nat := 486352958038439774831551

theorem tailTrace_2841507 : CollatzResearch.WordTrace tailWord_2841507 prefixEnd_2841507 486352958038439774831551 := by
  unfold tailWord_2841507
  simp only [CollatzResearch.WordTrace]
  refine ⟨103638274516712904604738775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69092183011141936403159183 103638274516712904604738775)
  ·
    refine ⟨155457411775069356907108163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103638274516712904604738775 155457411775069356907108163)
    ·
      refine ⟨233186117662604035360662245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155457411775069356907108163 233186117662604035360662245)
      ·
        refine ⟨43722397061738256630124171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233186117662604035360662245 43722397061738256630124171)
        ·
          refine ⟨65583595592607384945186257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43722397061738256630124171 65583595592607384945186257)
          ·
            refine ⟨49187696694455538708889693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65583595592607384945186257 49187696694455538708889693)
            ·
              refine ⟨18445386260420827015833635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49187696694455538708889693 18445386260420827015833635)
              ·
                refine ⟨27668079390631240523750453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18445386260420827015833635 27668079390631240523750453)
                ·
                  refine ⟨2593882442871678799101605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27668079390631240523750453 2593882442871678799101605)
                  ·
                    refine ⟨486352958038439774831551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2593882442871678799101605 486352958038439774831551)
                    ·
                      rfl

theorem cell23_2841507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 4].length) (baseStart_2841507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841507 prefixEnd_2841507 := by exact prefixLift 2841507
  have htrace : WordTrace (prefixWord ++ tailWord_2841507) baseStart_2841507 baseEnd_2841507 := by
    simpa [prefixWord, tailWord_2841507, baseEnd_2841507] using wordTrace_append hprefix tailTrace_2841507
  have hstable : (prefixWord ++ tailWord_2841507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841507).length < 2 ^ (prefixWord ++ tailWord_2841507).sum := by decide
  have hdescent : baseEnd_2841507 < baseStart_2841507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841511 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2841511 : Nat := 118140960795 + 2841511 * 2 ^ 59
def prefixEnd_2841511 : Nat := 4983230072969 + 3 ^ 40 * 2841511 * 2
def baseEnd_2841511 : Nat := 486353642679312436281545

theorem tailTrace_2841511 : CollatzResearch.WordTrace tailWord_2841511 prefixEnd_2841511 486353642679312436281545 := by
  unfold tailWord_2841511
  simp only [CollatzResearch.WordTrace]
  refine ⟨103638420408698413287884387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69092280272465608858589591 103638420408698413287884387)
  ·
    refine ⟨155457630613047619931826581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103638420408698413287884387 155457630613047619931826581)
    ·
      refine ⟨7287076434986607184304371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155457630613047619931826581 7287076434986607184304371)
      ·
        refine ⟨10930614652479910776456557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7287076434986607184304371 10930614652479910776456557)
        ·
          refine ⟨4098980494679966541171209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10930614652479910776456557 4098980494679966541171209)
          ·
            refine ⟨3074235371009974905878407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4098980494679966541171209 3074235371009974905878407)
            ·
              refine ⟨4611353056514962358817611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3074235371009974905878407 4611353056514962358817611)
              ·
                refine ⟨6917029584772443538226417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4611353056514962358817611 6917029584772443538226417)
                ·
                  refine ⟨5187772188579332653669813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6917029584772443538226417 5187772188579332653669813)
                  ·
                    refine ⟨486353642679312436281545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5187772188579332653669813 486353642679312436281545)
                    ·
                      rfl

theorem cell23_2841511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2841511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841511 prefixEnd_2841511 := by exact prefixLift 2841511
  have htrace : WordTrace (prefixWord ++ tailWord_2841511) baseStart_2841511 baseEnd_2841511 := by
    simpa [prefixWord, tailWord_2841511, baseEnd_2841511] using wordTrace_append hprefix tailTrace_2841511
  have hstable : (prefixWord ++ tailWord_2841511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841511).length < 2 ^ (prefixWord ++ tailWord_2841511).sum := by decide
  have hdescent : baseEnd_2841511 < baseStart_2841511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841526 : List Nat := [5, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2841526 : Nat := 118140960795 + 2841526 * 2 ^ 59
def prefixEnd_2841526 : Nat := 4983230072969 + 3 ^ 40 * 2841526 * 2
def baseEnd_2841526 : Nat := 1459068630247754750157067

theorem tailTrace_2841526 : CollatzResearch.WordTrace tailWord_2841526 prefixEnd_2841526 1459068630247754750157067 := by
  unfold tailWord_2841526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6477435468977754428105027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69092645002429380566453621 6477435468977754428105027)
  ·
    refine ⟨9716153203466631642157541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6477435468977754428105027 9716153203466631642157541)
    ·
      refine ⟨1821778725649993432904539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9716153203466631642157541 1821778725649993432904539)
      ·
        refine ⟨2732668088474990149356809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1821778725649993432904539 2732668088474990149356809)
        ·
          refine ⟨2049501066356242612017607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2732668088474990149356809 2049501066356242612017607)
          ·
            refine ⟨3074251599534363918026411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049501066356242612017607 3074251599534363918026411)
            ·
              refine ⟨4611377399301545877039617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3074251599534363918026411 4611377399301545877039617)
              ·
                refine ⟨3458533049476159407779713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4611377399301545877039617 3458533049476159407779713)
                ·
                  refine ⟨2593899787107119555834785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3458533049476159407779713 2593899787107119555834785)
                  ·
                    refine ⟨1945424840330339666876089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2593899787107119555834785 1945424840330339666876089)
                    ·
                      refine ⟨1459068630247754750157067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1945424840330339666876089 1459068630247754750157067)
                      ·
                        rfl

theorem cell23_2841526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2841526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841526 prefixEnd_2841526 := by exact prefixLift 2841526
  have htrace : WordTrace (prefixWord ++ tailWord_2841526) baseStart_2841526 baseEnd_2841526 := by
    simpa [prefixWord, tailWord_2841526, baseEnd_2841526] using wordTrace_append hprefix tailTrace_2841526
  have hstable : (prefixWord ++ tailWord_2841526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841526).length < 2 ^ (prefixWord ++ tailWord_2841526).sum := by decide
  have hdescent : baseEnd_2841526 < baseStart_2841526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841534 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_2841534 : Nat := 118140960795 + 2841534 * 2 ^ 59
def prefixEnd_2841534 : Nat := 4983230072969 + 3 ^ 40 * 2841534 * 2
def baseEnd_2841534 : Nat := 1459072738092990718857029

theorem tailTrace_2841534 : CollatzResearch.WordTrace tailWord_2841534 prefixEnd_2841534 1459072738092990718857029 := by
  unfold tailWord_2841534
  simp only [CollatzResearch.WordTrace]
  refine ⟨12954907410951886026996457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69092839525076725477314437 12954907410951886026996457)
  ·
    refine ⟨9716180558213914520247343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12954907410951886026996457 9716180558213914520247343)
    ·
      refine ⟨14574270837320871780371015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9716180558213914520247343 14574270837320871780371015)
      ·
        refine ⟨21861406255981307670556523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14574270837320871780371015 21861406255981307670556523)
        ·
          refine ⟨32792109383971961505834785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21861406255981307670556523 32792109383971961505834785)
          ·
            refine ⟨24594082037978971129376089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32792109383971961505834785 24594082037978971129376089)
            ·
              refine ⟨18445561528484228347032067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24594082037978971129376089 18445561528484228347032067)
              ·
                refine ⟨27668342292726342520548101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18445561528484228347032067 27668342292726342520548101)
                ·
                  refine ⟨5187814179886189222602769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27668342292726342520548101 5187814179886189222602769)
                  ·
                    refine ⟨3890860634914641916952077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5187814179886189222602769 3890860634914641916952077)
                    ·
                      refine ⟨1459072738092990718857029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3890860634914641916952077 1459072738092990718857029)
                      ·
                        rfl

theorem cell23_2841534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_2841534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841534 prefixEnd_2841534 := by exact prefixLift 2841534
  have htrace : WordTrace (prefixWord ++ tailWord_2841534) baseStart_2841534 baseEnd_2841534 := by
    simpa [prefixWord, tailWord_2841534, baseEnd_2841534] using wordTrace_append hprefix tailTrace_2841534
  have hstable : (prefixWord ++ tailWord_2841534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841534).length < 2 ^ (prefixWord ++ tailWord_2841534).sum := by decide
  have hdescent : baseEnd_2841534 < baseStart_2841534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841587 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 4]
def baseStart_2841587 : Nat := 118140960795 + 2841587 * 2 ^ 59
def prefixEnd_2841587 : Nat := 4983230072969 + 3 ^ 40 * 2841587 * 2
def baseEnd_2841587 : Nat := 1459099952567679011494285

theorem tailTrace_2841587 : CollatzResearch.WordTrace tailWord_2841587 prefixEnd_2841587 1459099952567679011494285 := by
  unfold tailWord_2841587
  simp only [CollatzResearch.WordTrace]
  refine ⟨103641192356423078267651015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69094128237615385511767343 103641192356423078267651015)
  ·
    refine ⟨155461788534634617401476523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103641192356423078267651015 155461788534634617401476523)
    ·
      refine ⟨233192682801951926102214785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155461788534634617401476523 233192682801951926102214785)
      ·
        refine ⟨174894512101463944576661089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233192682801951926102214785 174894512101463944576661089)
        ·
          refine ⟨131170884076097958432495817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174894512101463944576661089 131170884076097958432495817)
          ·
            refine ⟨98378163057073468824371863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131170884076097958432495817 98378163057073468824371863)
            ·
              refine ⟨147567244585610203236557795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98378163057073468824371863 147567244585610203236557795)
              ·
                refine ⟨221350866878415304854836693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147567244585610203236557795 221350866878415304854836693)
                ·
                  refine ⟨5187910942462858707535235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 221350866878415304854836693 5187910942462858707535235)
                  ·
                    refine ⟨7781866413694288061302853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5187910942462858707535235 7781866413694288061302853)
                    ·
                      refine ⟨1459099952567679011494285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7781866413694288061302853 1459099952567679011494285)
                      ·
                        rfl

theorem cell23_2841587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_2841587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841587 prefixEnd_2841587 := by exact prefixLift 2841587
  have htrace : WordTrace (prefixWord ++ tailWord_2841587) baseStart_2841587 baseEnd_2841587 := by
    simpa [prefixWord, tailWord_2841587, baseEnd_2841587] using wordTrace_append hprefix tailTrace_2841587
  have hstable : (prefixWord ++ tailWord_2841587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841587).length < 2 ^ (prefixWord ++ tailWord_2841587).sum := by decide
  have hdescent : baseEnd_2841587 < baseStart_2841587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841617 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_2841617 : Nat := 118140960795 + 2841617 * 2 ^ 59
def prefixEnd_2841617 : Nat := 4983230072969 + 3 ^ 40 * 2841617 * 2
def baseEnd_2841617 : Nat := 1459115356987313894119147

theorem tailTrace_2841617 : CollatzResearch.WordTrace tailWord_2841617 prefixEnd_2841617 1459115356987313894119147 := by
  unfold tailWord_2841617
  simp only [CollatzResearch.WordTrace]
  refine ⟨103642286546314393391243105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69094857697542928927495403 103642286546314393391243105)
  ·
    refine ⟨77731714909735795043432329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103642286546314393391243105 77731714909735795043432329)
    ·
      refine ⟨58298786182301846282574247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77731714909735795043432329 58298786182301846282574247)
      ·
        refine ⟨87448179273452769423861371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58298786182301846282574247 87448179273452769423861371)
        ·
          refine ⟨131172268910179154135792057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87448179273452769423861371 131172268910179154135792057)
          ·
            refine ⟨98379201682634365601844043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131172268910179154135792057 98379201682634365601844043)
            ·
              refine ⟨147568802523951548402766065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98379201682634365601844043 147568802523951548402766065)
              ·
                refine ⟨110676601892963661302074549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147568802523951548402766065 110676601892963661302074549)
                ·
                  refine ⟨10375931427465343247069489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110676601892963661302074549 10375931427465343247069489)
                  ·
                    refine ⟨7781948570599007435302117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10375931427465343247069489 7781948570599007435302117)
                    ·
                      refine ⟨1459115356987313894119147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7781948570599007435302117 1459115356987313894119147)
                      ·
                        rfl

theorem cell23_2841617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_2841617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841617 prefixEnd_2841617 := by exact prefixLift 2841617
  have htrace : WordTrace (prefixWord ++ tailWord_2841617) baseStart_2841617 baseEnd_2841617 := by
    simpa [prefixWord, tailWord_2841617, baseEnd_2841617] using wordTrace_append hprefix tailTrace_2841617
  have hstable : (prefixWord ++ tailWord_2841617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841617).length < 2 ^ (prefixWord ++ tailWord_2841617).sum := by decide
  have hdescent : baseEnd_2841617 < baseStart_2841617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841621 : List Nat := [1, 3, 2, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_2841621 : Nat := 118140960795 + 2841621 * 2 ^ 59
def prefixEnd_2841621 : Nat := 4983230072969 + 3 ^ 40 * 2841621 * 2
def baseEnd_2841621 : Nat := 1459117410909931878469129

theorem tailTrace_2841621 : CollatzResearch.WordTrace tailWord_2841621 prefixEnd_2841621 1459117410909931878469129 := by
  unfold tailWord_2841621
  simp only [CollatzResearch.WordTrace]
  refine ⟨103642432438299902074388717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69094954958866601382925811 103642432438299902074388717)
  ·
    refine ⟨38865912164362463277895769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103642432438299902074388717 38865912164362463277895769)
    ·
      refine ⟨29149434123271847458421827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38865912164362463277895769 29149434123271847458421827)
      ·
        refine ⟨43724151184907771187632741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29149434123271847458421827 43724151184907771187632741)
        ·
          refine ⟨8198278347170207097681139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43724151184907771187632741 8198278347170207097681139)
          ·
            refine ⟨12297417520755310646521709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8198278347170207097681139 12297417520755310646521709)
            ·
              refine ⟨4611531570283241492445641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12297417520755310646521709 4611531570283241492445641)
              ·
                refine ⟨3458648677712431119334231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4611531570283241492445641 3458648677712431119334231)
                ·
                  refine ⟨5187973016568646679001347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458648677712431119334231 5187973016568646679001347)
                  ·
                    refine ⟨7781959524852970018502021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5187973016568646679001347 7781959524852970018502021)
                    ·
                      refine ⟨1459117410909931878469129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7781959524852970018502021 1459117410909931878469129)
                      ·
                        rfl

theorem cell23_2841621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_2841621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841621 prefixEnd_2841621 := by exact prefixLift 2841621
  have htrace : WordTrace (prefixWord ++ tailWord_2841621) baseStart_2841621 baseEnd_2841621 := by
    simpa [prefixWord, tailWord_2841621, baseEnd_2841621] using wordTrace_append hprefix tailTrace_2841621
  have hstable : (prefixWord ++ tailWord_2841621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841621).length < 2 ^ (prefixWord ++ tailWord_2841621).sum := by decide
  have hdescent : baseEnd_2841621 < baseStart_2841621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841634 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_2841634 : Nat := 118140960795 + 2841634 * 2 ^ 59
def prefixEnd_2841634 : Nat := 4983230072969 + 3 ^ 40 * 2841634 * 2
def baseEnd_2841634 : Nat := 1459124086158440327606569

theorem tailTrace_2841634 : CollatzResearch.WordTrace tailWord_2841634 prefixEnd_2841634 1459124086158440327606569 := by
  unfold tailWord_2841634
  simp only [CollatzResearch.WordTrace]
  refine ⟨25910726646813201323652989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69095271058168536863074637 25910726646813201323652989)
  ·
    refine ⟨9716522492554950496369871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25910726646813201323652989 9716522492554950496369871)
    ·
      refine ⟨14574783738832425744554807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9716522492554950496369871 14574783738832425744554807)
      ·
        refine ⟨21862175608248638616832211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14574783738832425744554807 21862175608248638616832211)
        ·
          refine ⟨32793263412372957925248317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21862175608248638616832211 32793263412372957925248317)
          ·
            refine ⟨12297473779639859221968119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32793263412372957925248317 12297473779639859221968119)
            ·
              refine ⟨18446210669459788832952179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12297473779639859221968119 18446210669459788832952179)
              ·
                refine ⟨27669316004189683249428269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18446210669459788832952179 27669316004189683249428269)
                ·
                  refine ⟨10375993501571131218535601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27669316004189683249428269 10375993501571131218535601)
                  ·
                    refine ⟨7781995126178348413901701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10375993501571131218535601 7781995126178348413901701)
                    ·
                      refine ⟨1459124086158440327606569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7781995126178348413901701 1459124086158440327606569)
                      ·
                        rfl

theorem cell23_2841634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_2841634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841634 prefixEnd_2841634 := by exact prefixLift 2841634
  have htrace : WordTrace (prefixWord ++ tailWord_2841634) baseStart_2841634 baseEnd_2841634 := by
    simpa [prefixWord, tailWord_2841634, baseEnd_2841634] using wordTrace_append hprefix tailTrace_2841634
  have hstable : (prefixWord ++ tailWord_2841634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841634).length < 2 ^ (prefixWord ++ tailWord_2841634).sum := by decide
  have hdescent : baseEnd_2841634 < baseStart_2841634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841671 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_2841671 : Nat := 118140960795 + 2841671 * 2 ^ 59
def prefixEnd_2841671 : Nat := 4983230072969 + 3 ^ 40 * 2841671 * 2
def baseEnd_2841671 : Nat := 1459143084942656682843899

theorem tailTrace_2841671 : CollatzResearch.WordTrace tailWord_2841671 prefixEnd_2841671 1459143084942656682843899 := by
  unfold tailWord_2841671
  simp only [CollatzResearch.WordTrace]
  refine ⟨103644256088118760613708867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69096170725412507075805911 103644256088118760613708867)
  ·
    refine ⟨155466384132178140920563301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103644256088118760613708867 155466384132178140920563301)
    ·
      refine ⟨29149947024783401422605619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155466384132178140920563301 29149947024783401422605619)
      ·
        refine ⟨43724920537175102133908429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29149947024783401422605619 43724920537175102133908429)
        ·
          refine ⟨16396845201440663300215661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43724920537175102133908429 16396845201440663300215661)
          ·
            refine ⟨6148816950540248737580873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16396845201440663300215661 6148816950540248737580873)
            ·
              refine ⟨4611612712905186553185655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6148816950540248737580873 4611612712905186553185655)
              ·
                refine ⟨6917419069357779829778483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4611612712905186553185655 6917419069357779829778483)
                ·
                  refine ⟨10376128604036669744667725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6917419069357779829778483 10376128604036669744667725)
                  ·
                    refine ⟨3891048226513751154250397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10376128604036669744667725 3891048226513751154250397)
                    ·
                      refine ⟨1459143084942656682843899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3891048226513751154250397 1459143084942656682843899)
                      ·
                        rfl

theorem cell23_2841671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_2841671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841671 prefixEnd_2841671 := by exact prefixLift 2841671
  have htrace : WordTrace (prefixWord ++ tailWord_2841671) baseStart_2841671 baseEnd_2841671 := by
    simpa [prefixWord, tailWord_2841671, baseEnd_2841671] using wordTrace_append hprefix tailTrace_2841671
  have hstable : (prefixWord ++ tailWord_2841671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841671).length < 2 ^ (prefixWord ++ tailWord_2841671).sum := by decide
  have hdescent : baseEnd_2841671 < baseStart_2841671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841681 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 3, 3, 2]
def baseStart_2841681 : Nat := 118140960795 + 2841681 * 2 ^ 59
def prefixEnd_2841681 : Nat := 4983230072969 + 3 ^ 40 * 2841681 * 2
def baseEnd_2841681 : Nat := 1459148219749201643718853

theorem tailTrace_2841681 : CollatzResearch.WordTrace tailWord_2841681 prefixEnd_2841681 1459148219749201643718853 := by
  unfold tailWord_2841681
  simp only [CollatzResearch.WordTrace]
  refine ⟨103644620818082532321572897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69096413878721688214381931 103644620818082532321572897)
  ·
    refine ⟨77733465613561899241179673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103644620818082532321572897 77733465613561899241179673)
    ·
      refine ⟨58300099210171424430884755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77733465613561899241179673 58300099210171424430884755)
      ·
        refine ⟨87450148815257136646327133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58300099210171424430884755 87450148815257136646327133)
        ·
          refine ⟨32793805805721426242372675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87450148815257136646327133 32793805805721426242372675)
          ·
            refine ⟨49190708708582139363559013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32793805805721426242372675 49190708708582139363559013)
            ·
              refine ⟨9223257882859151130667315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49190708708582139363559013 9223257882859151130667315)
              ·
                refine ⟨13834886824288726696000973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9223257882859151130667315 13834886824288726696000973)
                ·
                  refine ⟨5188082559108272511000365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13834886824288726696000973 5188082559108272511000365)
                  ·
                    refine ⟨1945530959665602191625137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5188082559108272511000365 1945530959665602191625137)
                    ·
                      refine ⟨1459148219749201643718853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1945530959665602191625137 1459148219749201643718853)
                      ·
                        rfl

theorem cell23_2841681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 3, 2].length) (baseStart_2841681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841681 prefixEnd_2841681 := by exact prefixLift 2841681
  have htrace : WordTrace (prefixWord ++ tailWord_2841681) baseStart_2841681 baseEnd_2841681 := by
    simpa [prefixWord, tailWord_2841681, baseEnd_2841681] using wordTrace_append hprefix tailTrace_2841681
  have hstable : (prefixWord ++ tailWord_2841681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841681).length < 2 ^ (prefixWord ++ tailWord_2841681).sum := by decide
  have hdescent : baseEnd_2841681 < baseStart_2841681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841687 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 3, 8]
def baseStart_2841687 : Nat := 118140960795 + 2841687 * 2 ^ 59
def prefixEnd_2841687 : Nat := 4983230072969 + 3 ^ 40 * 2841687 * 2
def baseEnd_2841687 : Nat := 486383766877709540081275

theorem tailTrace_2841687 : CollatzResearch.WordTrace tailWord_2841687 prefixEnd_2841687 486383766877709540081275 := by
  unfold tailWord_2841687
  simp only [CollatzResearch.WordTrace]
  refine ⟨103644839656060795346291315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69096559770707196897527543 103644839656060795346291315)
  ·
    refine ⟨155467259484091193019436973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103644839656060795346291315 155467259484091193019436973)
    ·
      refine ⟨58300222306534197382288865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155467259484091193019436973 58300222306534197382288865)
      ·
        refine ⟨43725166729900648036716649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58300222306534197382288865 43725166729900648036716649)
        ·
          refine ⟨32793875047425486027537487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43725166729900648036716649 32793875047425486027537487)
          ·
            refine ⟨49190812571138229041306231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32793875047425486027537487 49190812571138229041306231)
            ·
              refine ⟨73786218856707343561959347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49190812571138229041306231 73786218856707343561959347)
              ·
                refine ⟨110679328285061015342939021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73786218856707343561959347 110679328285061015342939021)
                ·
                  refine ⟨41504748106897880753602133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110679328285061015342939021 41504748106897880753602133)
                  ·
                    refine ⟨486383766877709540081275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41504748106897880753602133 486383766877709540081275)
                    ·
                      rfl

theorem cell23_2841687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_2841687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841687 prefixEnd_2841687 := by exact prefixLift 2841687
  have htrace : WordTrace (prefixWord ++ tailWord_2841687) baseStart_2841687 baseEnd_2841687 := by
    simpa [prefixWord, tailWord_2841687, baseEnd_2841687] using wordTrace_append hprefix tailTrace_2841687
  have hstable : (prefixWord ++ tailWord_2841687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841687).length < 2 ^ (prefixWord ++ tailWord_2841687).sum := by decide
  have hdescent : baseEnd_2841687 < baseStart_2841687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841724 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_2841724 : Nat := 118140960795 + 2841724 * 2 ^ 59
def prefixEnd_2841724 : Nat := 4983230072969 + 3 ^ 40 * 2841724 * 2
def baseEnd_2841724 : Nat := 1459170299417344975481155

theorem tailTrace_2841724 : CollatzResearch.WordTrace tailWord_2841724 prefixEnd_2841724 1459170299417344975481155 := by
  unfold tailWord_2841724
  simp only [CollatzResearch.WordTrace]
  refine ⟨51823094578463375332694113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69097459437951167110258817 51823094578463375332694113)
  ·
    refine ⟨38867320933847531499520585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51823094578463375332694113 38867320933847531499520585)
    ·
      refine ⟨29150490700385648624640439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38867320933847531499520585 29150490700385648624640439)
      ·
        refine ⟨43725736050578472936960659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29150490700385648624640439 43725736050578472936960659)
        ·
          refine ⟨65588604075867709405440989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43725736050578472936960659 65588604075867709405440989)
          ·
            refine ⟨24595726528450391027040371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65588604075867709405440989 24595726528450391027040371)
            ·
              refine ⟨36893589792675586540560557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24595726528450391027040371 36893589792675586540560557)
              ·
                refine ⟨13835096172253344952710209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36893589792675586540560557 13835096172253344952710209)
                ·
                  refine ⟨10376322129190008714532657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13835096172253344952710209 10376322129190008714532657)
                  ·
                    refine ⟨7782241596892506535899493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10376322129190008714532657 7782241596892506535899493)
                    ·
                      refine ⟨1459170299417344975481155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7782241596892506535899493 1459170299417344975481155)
                      ·
                        rfl

theorem cell23_2841724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_2841724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841724 prefixEnd_2841724 := by exact prefixLift 2841724
  have htrace : WordTrace (prefixWord ++ tailWord_2841724) baseStart_2841724 baseEnd_2841724 := by
    simpa [prefixWord, tailWord_2841724, baseEnd_2841724] using wordTrace_append hprefix tailTrace_2841724
  have hstable : (prefixWord ++ tailWord_2841724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841724).length < 2 ^ (prefixWord ++ tailWord_2841724).sum := by decide
  have hdescent : baseEnd_2841724 < baseStart_2841724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841727 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 9]
def baseStart_2841727 : Nat := 118140960795 + 2841727 * 2 ^ 59
def prefixEnd_2841727 : Nat := 4983230072969 + 3 ^ 40 * 2841727 * 2
def baseEnd_2841727 : Nat := 1459171839859308463743641

theorem tailTrace_2841727 : CollatzResearch.WordTrace tailWord_2841727 prefixEnd_2841727 1459171839859308463743641 := by
  unfold tailWord_2841727
  simp only [CollatzResearch.WordTrace]
  refine ⟨103646298575915882177747435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69097532383943921451831623 103646298575915882177747435)
  ·
    refine ⟨155469447863873823266621153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103646298575915882177747435 155469447863873823266621153)
    ·
      refine ⟨116602085897905367449965865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155469447863873823266621153 116602085897905367449965865)
      ·
        refine ⟨87451564423429025587474399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116602085897905367449965865 87451564423429025587474399)
        ·
          refine ⟨131177346635143538381211599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87451564423429025587474399 131177346635143538381211599)
          ·
            refine ⟨196766019952715307571817399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131177346635143538381211599 196766019952715307571817399)
            ·
              refine ⟨295149029929072961357726099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196766019952715307571817399 295149029929072961357726099)
              ·
                refine ⟨442723544893609442036589149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295149029929072961357726099 442723544893609442036589149)
                ·
                  refine ⟨166021329335103540763720931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 442723544893609442036589149 166021329335103540763720931)
                  ·
                    refine ⟨249031994002655311145581397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166021329335103540763720931 249031994002655311145581397)
                    ·
                      refine ⟨1459171839859308463743641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 249031994002655311145581397 1459171839859308463743641)
                      ·
                        rfl

theorem cell23_2841727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_2841727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841727 prefixEnd_2841727 := by exact prefixLift 2841727
  have htrace : WordTrace (prefixWord ++ tailWord_2841727) baseStart_2841727 baseEnd_2841727 := by
    simpa [prefixWord, tailWord_2841727, baseEnd_2841727] using wordTrace_append hprefix tailTrace_2841727
  have hstable : (prefixWord ++ tailWord_2841727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841727).length < 2 ^ (prefixWord ++ tailWord_2841727).sum := by decide
  have hdescent : baseEnd_2841727 < baseStart_2841727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841728 : List Nat := [2, 1, 1, 2, 1, 3, 2, 5, 2, 2, 2]
def baseStart_2841728 : Nat := 118140960795 + 2841728 * 2 ^ 59
def prefixEnd_2841728 : Nat := 4983230072969 + 3 ^ 40 * 2841728 * 2
def baseEnd_2841728 : Nat := 1459172353339962959831137

theorem tailTrace_2841728 : CollatzResearch.WordTrace tailWord_2841728 prefixEnd_2841728 1459172353339962959831137 := by
  unfold tailWord_2841728
  simp only [CollatzResearch.WordTrace]
  refine ⟨51823167524456129674266919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69097556699274839565689225 51823167524456129674266919)
  ·
    refine ⟨77734751286684194511400379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51823167524456129674266919 77734751286684194511400379)
    ·
      refine ⟨116602126930026291767100569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77734751286684194511400379 116602126930026291767100569)
      ·
        refine ⟨87451595197519718825325427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116602126930026291767100569 87451595197519718825325427)
        ·
          refine ⟨131177392796279578237988141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87451595197519718825325427 131177392796279578237988141)
          ·
            refine ⟨49191522298604841839245553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131177392796279578237988141 49191522298604841839245553)
            ·
              refine ⟨36893641723953631379434165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49191522298604841839245553 36893641723953631379434165)
              ·
                refine ⟨3458778911620652941821953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36893641723953631379434165 3458778911620652941821953)
                ·
                  refine ⟨2594084183715489706366465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3458778911620652941821953 2594084183715489706366465)
                  ·
                    refine ⟨1945563137786617279774849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2594084183715489706366465 1945563137786617279774849)
                    ·
                      refine ⟨1459172353339962959831137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1945563137786617279774849 1459172353339962959831137)
                      ·
                        rfl

theorem cell23_2841728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 2, 2, 2].length) (baseStart_2841728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841728 prefixEnd_2841728 := by exact prefixLift 2841728
  have htrace : WordTrace (prefixWord ++ tailWord_2841728) baseStart_2841728 baseEnd_2841728 := by
    simpa [prefixWord, tailWord_2841728, baseEnd_2841728] using wordTrace_append hprefix tailTrace_2841728
  have hstable : (prefixWord ++ tailWord_2841728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841728).length < 2 ^ (prefixWord ++ tailWord_2841728).sum := by decide
  have hdescent : baseEnd_2841728 < baseStart_2841728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841744 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 3]
def baseStart_2841744 : Nat := 118140960795 + 2841744 * 2 ^ 59
def prefixEnd_2841744 : Nat := 4983230072969 + 3 ^ 40 * 2841744 * 2
def baseEnd_2841744 : Nat := 1459180569030434897231063

theorem tailTrace_2841744 : CollatzResearch.WordTrace tailWord_2841744 prefixEnd_2841744 1459180569030434897231063 := by
  unfold tailWord_2841744
  simp only [CollatzResearch.WordTrace]
  refine ⟨51823459308427147040558143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69097945744569529387410857 51823459308427147040558143)
  ·
    refine ⟨77735188962640720560837215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51823459308427147040558143 77735188962640720560837215)
    ·
      refine ⟨116602783443961080841255823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77735188962640720560837215 116602783443961080841255823)
      ·
        refine ⟨174904175165941621261883735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116602783443961080841255823 174904175165941621261883735)
        ·
          refine ⟨262356262748912431892825603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174904175165941621261883735 262356262748912431892825603)
          ·
            refine ⟨393534394123368647839238405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262356262748912431892825603 393534394123368647839238405)
            ·
              refine ⟨73787698898131621469857201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 393534394123368647839238405 73787698898131621469857201)
              ·
                refine ⟨55340774173598716102392901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73787698898131621469857201 55340774173598716102392901)
                ·
                  refine ⟨10376395157549759269198669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55340774173598716102392901 10376395157549759269198669)
                  ·
                    refine ⟨3891148184081159725949501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10376395157549759269198669 3891148184081159725949501)
                    ·
                      refine ⟨1459180569030434897231063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3891148184081159725949501 1459180569030434897231063)
                      ·
                        rfl

theorem cell23_2841744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 3].length) (baseStart_2841744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841744 prefixEnd_2841744 := by exact prefixLift 2841744
  have htrace : WordTrace (prefixWord ++ tailWord_2841744) baseStart_2841744 baseEnd_2841744 := by
    simpa [prefixWord, tailWord_2841744, baseEnd_2841744] using wordTrace_append hprefix tailTrace_2841744
  have hstable : (prefixWord ++ tailWord_2841744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841744).length < 2 ^ (prefixWord ++ tailWord_2841744).sum := by decide
  have hdescent : baseEnd_2841744 < baseStart_2841744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841784 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_2841784 : Nat := 118140960795 + 2841784 * 2 ^ 59
def prefixEnd_2841784 : Nat := 4983230072969 + 3 ^ 40 * 2841784 * 2
def baseEnd_2841784 : Nat := 1459201108256614740730879

theorem tailTrace_2841784 : CollatzResearch.WordTrace tailWord_2841784 prefixEnd_2841784 1459201108256614740730879 := by
  unfold tailWord_2841784
  simp only [CollatzResearch.WordTrace]
  refine ⟨51824188768354690456286203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69098918357806253941714937 51824188768354690456286203)
  ·
    refine ⟨77736283152532035684429305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51824188768354690456286203 77736283152532035684429305)
    ·
      refine ⟨58302212364399026763321979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77736283152532035684429305 58302212364399026763321979)
      ·
        refine ⟨87453318546598540144982969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58302212364399026763321979 87453318546598540144982969)
        ·
          refine ⟨65589988909948905108737227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87453318546598540144982969 65589988909948905108737227)
          ·
            refine ⟨98384983364923357663105841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65589988909948905108737227 98384983364923357663105841)
            ·
              refine ⟨73788737523692518247329381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98384983364923357663105841 73788737523692518247329381)
              ·
                refine ⟨13835388285692347171374259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73788737523692518247329381 13835388285692347171374259)
                ·
                  refine ⟨20753082428538520757061389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13835388285692347171374259 20753082428538520757061389)
                  ·
                    refine ⟨7782405910701945283898021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20753082428538520757061389 7782405910701945283898021)
                    ·
                      refine ⟨1459201108256614740730879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7782405910701945283898021 1459201108256614740730879)
                      ·
                        rfl

theorem cell23_2841784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_2841784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841784 prefixEnd_2841784 := by exact prefixLift 2841784
  have htrace : WordTrace (prefixWord ++ tailWord_2841784) baseStart_2841784 baseEnd_2841784 := by
    simpa [prefixWord, tailWord_2841784, baseEnd_2841784] using wordTrace_append hprefix tailTrace_2841784
  have hstable : (prefixWord ++ tailWord_2841784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841784).length < 2 ^ (prefixWord ++ tailWord_2841784).sum := by decide
  have hdescent : baseEnd_2841784 < baseStart_2841784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841885 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_2841885 : Nat := 118140960795 + 2841885 * 2 ^ 59
def prefixEnd_2841885 : Nat := 4983230072969 + 3 ^ 40 * 2841885 * 2
def baseEnd_2841885 : Nat := 1459252969802718845567915

theorem tailTrace_2841885 : CollatzResearch.WordTrace tailWord_2841885 prefixEnd_2841885 1459252969802718845567915 := by
  unfold tailWord_2841885
  simp only [CollatzResearch.WordTrace]
  refine ⟨103652061309343475161999109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69101374206228983441332739 103652061309343475161999109)
  ·
    refine ⟨19434761495501901592874833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103652061309343475161999109 19434761495501901592874833)
    ·
      refine ⟨14576071121626426194656125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19434761495501901592874833 14576071121626426194656125)
      ·
        refine ⟨5466026670609909822996047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14576071121626426194656125 5466026670609909822996047)
        ·
          refine ⟨8199040005914864734494071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5466026670609909822996047 8199040005914864734494071)
          ·
            refine ⟨12298560008872297101741107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8199040005914864734494071 12298560008872297101741107)
            ·
              refine ⟨18447840013308445652611661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12298560008872297101741107 18447840013308445652611661)
              ·
                refine ⟨6917940004990667119729373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18447840013308445652611661 6917940004990667119729373)
                ·
                  refine ⟨2594227501871500169898515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6917940004990667119729373 2594227501871500169898515)
                  ·
                    refine ⟨3891341252807250254847773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2594227501871500169898515 3891341252807250254847773)
                    ·
                      refine ⟨1459252969802718845567915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3891341252807250254847773 1459252969802718845567915)
                      ·
                        rfl

theorem cell23_2841885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_2841885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841885 prefixEnd_2841885 := by exact prefixLift 2841885
  have htrace : WordTrace (prefixWord ++ tailWord_2841885) baseStart_2841885 baseEnd_2841885 := by
    simpa [prefixWord, tailWord_2841885, baseEnd_2841885] using wordTrace_append hprefix tailTrace_2841885
  have hstable : (prefixWord ++ tailWord_2841885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841885).length < 2 ^ (prefixWord ++ tailWord_2841885).sum := by decide
  have hdescent : baseEnd_2841885 < baseStart_2841885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841918 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_2841918 : Nat := 118140960795 + 2841918 * 2 ^ 59
def prefixEnd_2841918 : Nat := 4983230072969 + 3 ^ 40 * 2841918 * 2
def baseEnd_2841918 : Nat := 486423304888105738818421

theorem tailTrace_2841918 : CollatzResearch.WordTrace tailWord_2841918 prefixEnd_2841918 486423304888105738818421 := by
  unfold tailWord_2841918
  simp only [CollatzResearch.WordTrace]
  refine ⟨12956658114777990224743801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69102176612149281198633605 12956658114777990224743801)
  ·
    refine ⟨9717493586083492668557851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12956658114777990224743801 9717493586083492668557851)
    ·
      refine ⟨14576240379125239002836777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9717493586083492668557851 14576240379125239002836777)
      ·
        refine ⟨10932180284343929252127583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14576240379125239002836777 10932180284343929252127583)
        ·
          refine ⟨16398270426515893878191375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10932180284343929252127583 16398270426515893878191375)
          ·
            refine ⟨24597405639773840817287063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16398270426515893878191375 24597405639773840817287063)
            ·
              refine ⟨36896108459660761225930595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24597405639773840817287063 36896108459660761225930595)
              ·
                refine ⟨55344162689491141838895893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36896108459660761225930595 55344162689491141838895893)
                ·
                  refine ⟨2594257626069897273698245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55344162689491141838895893 2594257626069897273698245)
                  ·
                    refine ⟨486423304888105738818421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2594257626069897273698245 486423304888105738818421)
                    ·
                      rfl

theorem cell23_2841918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_2841918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841918 prefixEnd_2841918 := by exact prefixLift 2841918
  have htrace : WordTrace (prefixWord ++ tailWord_2841918) baseStart_2841918 baseEnd_2841918 := by
    simpa [prefixWord, tailWord_2841918, baseEnd_2841918] using wordTrace_append hprefix tailTrace_2841918
  have hstable : (prefixWord ++ tailWord_2841918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841918).length < 2 ^ (prefixWord ++ tailWord_2841918).sum := by decide
  have hdescent : baseEnd_2841918 < baseStart_2841918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841952 : List Nat := [2, 1, 1, 3, 4, 3, 2, 1, 2, 4]
def baseStart_2841952 : Nat := 118140960795 + 2841952 * 2 ^ 59
def prefixEnd_2841952 : Nat := 4983230072969 + 3 ^ 40 * 2841952 * 2
def baseEnd_2841952 : Nat := 486429124335523361143369

theorem tailTrace_2841952 : CollatzResearch.WordTrace tailWord_2841952 prefixEnd_2841952 486429124335523361143369 := by
  unfold tailWord_2841952
  simp only [CollatzResearch.WordTrace]
  refine ⟨51827252500050372802344055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69103003333400497069792073 51827252500050372802344055)
  ·
    refine ⟨77740878750075559203516083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51827252500050372802344055 77740878750075559203516083)
    ·
      refine ⟨116611318125113338805274125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77740878750075559203516083 116611318125113338805274125)
      ·
        refine ⟨43729244296917502051977797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116611318125113338805274125 43729244296917502051977797)
        ·
          refine ⟨8199233305672031634745837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43729244296917502051977797 8199233305672031634745837)
          ·
            refine ⟨3074712489627011863029689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8199233305672031634745837 3074712489627011863029689)
            ·
              refine ⟨2306034367220258897272267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3074712489627011863029689 2306034367220258897272267)
              ·
                refine ⟨3459051550830388345908401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2306034367220258897272267 3459051550830388345908401)
                ·
                  refine ⟨2594288663122791259431301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3459051550830388345908401 2594288663122791259431301)
                  ·
                    refine ⟨486429124335523361143369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2594288663122791259431301 486429124335523361143369)
                    ·
                      rfl

theorem cell23_2841952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 2, 4].length) (baseStart_2841952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841952 prefixEnd_2841952 := by exact prefixLift 2841952
  have htrace : WordTrace (prefixWord ++ tailWord_2841952) baseStart_2841952 baseEnd_2841952 := by
    simpa [prefixWord, tailWord_2841952, baseEnd_2841952] using wordTrace_append hprefix tailTrace_2841952
  have hstable : (prefixWord ++ tailWord_2841952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841952).length < 2 ^ (prefixWord ++ tailWord_2841952).sum := by decide
  have hdescent : baseEnd_2841952 < baseStart_2841952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841992 : List Nat := [2, 1, 3, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2841992 : Nat := 118140960795 + 2841992 * 2 ^ 59
def prefixEnd_2841992 : Nat := 4983230072969 + 3 ^ 40 * 2841992 * 2
def baseEnd_2841992 : Nat := 1459307912232749926929923

theorem tailTrace_2841992 : CollatzResearch.WordTrace tailWord_2841992 prefixEnd_2841992 1459307912232749926929923 := by
  unfold tailWord_2841992
  simp only [CollatzResearch.WordTrace]
  refine ⟨51827981959977916218072115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69103975946637221624096153 51827981959977916218072115)
  ·
    refine ⟨77741972939966874327108173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51827981959977916218072115 77741972939966874327108173)
    ·
      refine ⟨29153239852487577872665565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77741972939966874327108173 29153239852487577872665565)
      ·
        refine ⟨10932464944682841702249587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29153239852487577872665565 10932464944682841702249587)
        ·
          refine ⟨16398697417024262553374381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10932464944682841702249587 16398697417024262553374381)
          ·
            refine ⟨6149511531384098457515393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16398697417024262553374381 6149511531384098457515393)
            ·
              refine ⟨4612133648538073843136545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6149511531384098457515393 4612133648538073843136545)
              ·
                refine ⟨3459100236403555382352409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4612133648538073843136545 3459100236403555382352409)
                ·
                  refine ⟨2594325177302666536764307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3459100236403555382352409 2594325177302666536764307)
                  ·
                    refine ⟨3891487765953999805146461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2594325177302666536764307 3891487765953999805146461)
                    ·
                      refine ⟨1459307912232749926929923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3891487765953999805146461 1459307912232749926929923)
                      ·
                        rfl

theorem cell23_2841992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2841992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841992 prefixEnd_2841992 := by exact prefixLift 2841992
  have htrace : WordTrace (prefixWord ++ tailWord_2841992) baseStart_2841992 baseEnd_2841992 := by
    simpa [prefixWord, tailWord_2841992, baseEnd_2841992] using wordTrace_append hprefix tailTrace_2841992
  have hstable : (prefixWord ++ tailWord_2841992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841992).length < 2 ^ (prefixWord ++ tailWord_2841992).sum := by decide
  have hdescent : baseEnd_2841992 < baseStart_2841992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2841993 : List Nat := [1, 2, 1, 1, 8, 1, 2, 2, 1, 2, 2]
def baseStart_2841993 : Nat := 118140960795 + 2841993 * 2 ^ 59
def prefixEnd_2841993 : Nat := 4983230072969 + 3 ^ 40 * 2841993 * 2
def baseEnd_2841993 : Nat := 1459308425713404423017419

theorem tailTrace_2841993 : CollatzResearch.WordTrace tailWord_2841993 prefixEnd_2841993 1459308425713404423017419 := by
  unfold tailWord_2841993
  simp only [CollatzResearch.WordTrace]
  refine ⟨103656000392952209606930633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69104000261968139737953755 103656000392952209606930633)
  ·
    refine ⟨77742000294714157205197975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103656000392952209606930633 77742000294714157205197975)
    ·
      refine ⟨116613000442071235807796963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77742000294714157205197975 116613000442071235807796963)
      ·
        refine ⟨174919500663106853711695445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116613000442071235807796963 174919500663106853711695445)
        ·
          refine ⟨2049837898395783441933931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 174919500663106853711695445 2049837898395783441933931)
          ·
            refine ⟨3074756847593675162900897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049837898395783441933931 3074756847593675162900897)
            ·
              refine ⟨2306067635695256372175673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3074756847593675162900897 2306067635695256372175673)
              ·
                refine ⟨1729550726771442279131755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2306067635695256372175673 1729550726771442279131755)
                ·
                  refine ⟨2594326090157163418697633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1729550726771442279131755 2594326090157163418697633)
                  ·
                    refine ⟨1945744567617872564023225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2594326090157163418697633 1945744567617872564023225)
                    ·
                      refine ⟨1459308425713404423017419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1945744567617872564023225 1459308425713404423017419)
                      ·
                        rfl

theorem cell23_2841993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 1, 2, 2].length) (baseStart_2841993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2841993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2841993 prefixEnd_2841993 := by exact prefixLift 2841993
  have htrace : WordTrace (prefixWord ++ tailWord_2841993) baseStart_2841993 baseEnd_2841993 := by
    simpa [prefixWord, tailWord_2841993, baseEnd_2841993] using wordTrace_append hprefix tailTrace_2841993
  have hstable : (prefixWord ++ tailWord_2841993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2841993).length < 2 ^ (prefixWord ++ tailWord_2841993).sum := by decide
  have hdescent : baseEnd_2841993 < baseStart_2841993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2841993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842011 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 4]
def baseStart_2842011 : Nat := 118140960795 + 2842011 * 2 ^ 59
def prefixEnd_2842011 : Nat := 4983230072969 + 3 ^ 40 * 2842011 * 2
def baseEnd_2842011 : Nat := 1459317668365185352592335

theorem tailTrace_2842011 : CollatzResearch.WordTrace tailWord_2842011 prefixEnd_2842011 1459317668365185352592335 := by
  unfold tailWord_2842011
  simp only [CollatzResearch.WordTrace]
  refine ⟨103656656906886998681085887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69104437937924665787390591 103656656906886998681085887)
  ·
    refine ⟨155484985360330498021628831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103656656906886998681085887 155484985360330498021628831)
    ·
      refine ⟨233227478040495747032443247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155484985360330498021628831 233227478040495747032443247)
      ·
        refine ⟨349841217060743620548664871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233227478040495747032443247 349841217060743620548664871)
        ·
          refine ⟨524761825591115430822997307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349841217060743620548664871 524761825591115430822997307)
          ·
            refine ⟨787142738386673146234495961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524761825591115430822997307 787142738386673146234495961)
            ·
              refine ⟨590357053790004859675871971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787142738386673146234495961 590357053790004859675871971)
              ·
                refine ⟨885535580685007289513807957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590357053790004859675871971 885535580685007289513807957)
                ·
                  refine ⟨10377370086152429173989937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 885535580685007289513807957 10377370086152429173989937)
                  ·
                    refine ⟨7783027564614321880492453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10377370086152429173989937 7783027564614321880492453)
                    ·
                      refine ⟨1459317668365185352592335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7783027564614321880492453 1459317668365185352592335)
                      ·
                        rfl

theorem cell23_2842011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 4].length) (baseStart_2842011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842011 prefixEnd_2842011 := by exact prefixLift 2842011
  have htrace : WordTrace (prefixWord ++ tailWord_2842011) baseStart_2842011 baseEnd_2842011 := by
    simpa [prefixWord, tailWord_2842011, baseEnd_2842011] using wordTrace_append hprefix tailTrace_2842011
  have hstable : (prefixWord ++ tailWord_2842011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842011).length < 2 ^ (prefixWord ++ tailWord_2842011).sum := by decide
  have hdescent : baseEnd_2842011 < baseStart_2842011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842015 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 1, 4, 2]
def baseStart_2842015 : Nat := 118140960795 + 2842015 * 2 ^ 59
def prefixEnd_2842015 : Nat := 4983230072969 + 3 ^ 40 * 2842015 * 2
def baseEnd_2842015 : Nat := 1459319722287803336942317

theorem tailTrace_2842015 : CollatzResearch.WordTrace tailWord_2842015 prefixEnd_2842015 1459319722287803336942317 := by
  unfold tailWord_2842015
  simp only [CollatzResearch.WordTrace]
  refine ⟨103656802798872507364231499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69104535199248338242820999 103656802798872507364231499)
  ·
    refine ⟨155485204198308761046347249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103656802798872507364231499 155485204198308761046347249)
    ·
      refine ⟨116613903148731570784760437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155485204198308761046347249 116613903148731570784760437)
      ·
        refine ⟨10932553420193584761071291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116613903148731570784760437 10932553420193584761071291)
        ·
          refine ⟨16398830130290377141606937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10932553420193584761071291 16398830130290377141606937)
          ·
            refine ⟨12299122597717782856205203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16398830130290377141606937 12299122597717782856205203)
            ·
              refine ⟨18448683896576674284307805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12299122597717782856205203 18448683896576674284307805)
              ·
                refine ⟨6918256461216252856615427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18448683896576674284307805 6918256461216252856615427)
                ·
                  refine ⟨10377384691824379284923141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6918256461216252856615427 10377384691824379284923141)
                  ·
                    refine ⟨1945759629717071115923089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10377384691824379284923141 1945759629717071115923089)
                    ·
                      refine ⟨1459319722287803336942317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1945759629717071115923089 1459319722287803336942317)
                      ·
                        rfl

theorem cell23_2842015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_2842015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842015 prefixEnd_2842015 := by exact prefixLift 2842015
  have htrace : WordTrace (prefixWord ++ tailWord_2842015) baseStart_2842015 baseEnd_2842015 := by
    simpa [prefixWord, tailWord_2842015, baseEnd_2842015] using wordTrace_append hprefix tailTrace_2842015
  have hstable : (prefixWord ++ tailWord_2842015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842015).length < 2 ^ (prefixWord ++ tailWord_2842015).sum := by decide
  have hdescent : baseEnd_2842015 < baseStart_2842015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842048 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 3]
def baseStart_2842048 : Nat := 118140960795 + 2842048 * 2 ^ 59
def prefixEnd_2842048 : Nat := 4983230072969 + 3 ^ 40 * 2842048 * 2
def baseEnd_2842048 : Nat := 1459336667149401707829665

theorem tailTrace_2842048 : CollatzResearch.WordTrace tailWord_2842048 prefixEnd_2842048 1459336667149401707829665 := by
  unfold tailWord_2842048
  simp only [CollatzResearch.WordTrace]
  refine ⟨51829003203876477000091399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69105337605168636000121865 51829003203876477000091399)
  ·
    refine ⟨77743504805814715500137099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51829003203876477000091399 77743504805814715500137099)
    ·
      refine ⟨116615257208722073250205649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77743504805814715500137099 116615257208722073250205649)
      ·
        refine ⟨87461442906541554937654237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116615257208722073250205649 87461442906541554937654237)
        ·
          refine ⟨32798041089953083101620339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87461442906541554937654237 32798041089953083101620339)
          ·
            refine ⟨49197061634929624652430509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32798041089953083101620339 49197061634929624652430509)
            ·
              refine ⟨18448898113098609244661441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49197061634929624652430509 18448898113098609244661441)
              ·
                refine ⟨13836673584823956933496081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18448898113098609244661441 13836673584823956933496081)
                ·
                  refine ⟨10377505188617967700122061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13836673584823956933496081 10377505188617967700122061)
                  ·
                    refine ⟨3891564445731737887545773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10377505188617967700122061 3891564445731737887545773)
                    ·
                      refine ⟨1459336667149401707829665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3891564445731737887545773 1459336667149401707829665)
                      ·
                        rfl

theorem cell23_2842048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_2842048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842048 prefixEnd_2842048 := by exact prefixLift 2842048
  have htrace : WordTrace (prefixWord ++ tailWord_2842048) baseStart_2842048 baseEnd_2842048 := by
    simpa [prefixWord, tailWord_2842048, baseEnd_2842048] using wordTrace_append hprefix tailTrace_2842048
  have hstable : (prefixWord ++ tailWord_2842048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842048).length < 2 ^ (prefixWord ++ tailWord_2842048).sum := by decide
  have hdescent : baseEnd_2842048 < baseStart_2842048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842088 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2842088 : Nat := 118140960795 + 2842088 * 2 ^ 59
def prefixEnd_2842088 : Nat := 4983230072969 + 3 ^ 40 * 2842088 * 2
def baseEnd_2842088 : Nat := 1459357206375581551329481

theorem tailTrace_2842088 : CollatzResearch.WordTrace tailWord_2842088 prefixEnd_2842088 1459357206375581551329481 := by
  unfold tailWord_2842088
  simp only [CollatzResearch.WordTrace]
  refine ⟨51829732663804020415819459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69106310218405360554425945 51829732663804020415819459)
  ·
    refine ⟨77744598995706030623729189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51829732663804020415819459 77744598995706030623729189)
    ·
      refine ⟨14577112311694880741949223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77744598995706030623729189 14577112311694880741949223)
      ·
        refine ⟨21865668467542321112923835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14577112311694880741949223 21865668467542321112923835)
        ·
          refine ⟨32798502701313481669385753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21865668467542321112923835 32798502701313481669385753)
          ·
            refine ⟨24598877025985111252039315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32798502701313481669385753 24598877025985111252039315)
            ·
              refine ⟨36898315538977666878058973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24598877025985111252039315 36898315538977666878058973)
              ·
                refine ⟨13836868327116625079272115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36898315538977666878058973 13836868327116625079272115)
                ·
                  refine ⟨20755302490674937618908173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13836868327116625079272115 20755302490674937618908173)
                  ·
                    refine ⟨7783238434003101607090565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20755302490674937618908173 7783238434003101607090565)
                    ·
                      refine ⟨1459357206375581551329481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7783238434003101607090565 1459357206375581551329481)
                      ·
                        rfl

theorem cell23_2842088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2842088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842088 prefixEnd_2842088 := by exact prefixLift 2842088
  have htrace : WordTrace (prefixWord ++ tailWord_2842088) baseStart_2842088 baseEnd_2842088 := by
    simpa [prefixWord, tailWord_2842088, baseEnd_2842088] using wordTrace_append hprefix tailTrace_2842088
  have hstable : (prefixWord ++ tailWord_2842088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842088).length < 2 ^ (prefixWord ++ tailWord_2842088).sum := by decide
  have hdescent : baseEnd_2842088 < baseStart_2842088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842166 : List Nat := [5, 1, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_2842166 : Nat := 118140960795 + 2842166 * 2 ^ 59
def prefixEnd_2842166 : Nat := 4983230072969 + 3 ^ 40 * 2842166 * 2
def baseEnd_2842166 : Nat := 486465752622210748718041

theorem tailTrace_2842166 : CollatzResearch.WordTrace tailWord_2842166 prefixEnd_2842166 486465752622210748718041 := by
  unfold tailWord_2842166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6478894388832841259561147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69108206814216973435318901 6478894388832841259561147)
  ·
    refine ⟨9718341583249261889341721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6478894388832841259561147 9718341583249261889341721)
    ·
      refine ⟨7288756187436946417006291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9718341583249261889341721 7288756187436946417006291)
      ·
        refine ⟨10933134281155419625509437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7288756187436946417006291 10933134281155419625509437)
        ·
          refine ⟨4099925355433282359566039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10933134281155419625509437 4099925355433282359566039)
          ·
            refine ⟨6149888033149923539349059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4099925355433282359566039 6149888033149923539349059)
            ·
              refine ⟨9224832049724885309023589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6149888033149923539349059 9224832049724885309023589)
              ·
                refine ⟨1729656009323415995441923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9224832049724885309023589 1729656009323415995441923)
                ·
                  refine ⟨2594484013985123993162885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1729656009323415995441923 2594484013985123993162885)
                  ·
                    refine ⟨486465752622210748718041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2594484013985123993162885 486465752622210748718041)
                    ·
                      rfl

theorem cell23_2842166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_2842166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842166 prefixEnd_2842166 := by exact prefixLift 2842166
  have htrace : WordTrace (prefixWord ++ tailWord_2842166) baseStart_2842166 baseEnd_2842166 := by
    simpa [prefixWord, tailWord_2842166, baseEnd_2842166] using wordTrace_append hprefix tailTrace_2842166
  have hstable : (prefixWord ++ tailWord_2842166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842166).length < 2 ^ (prefixWord ++ tailWord_2842166).sum := by decide
  have hdescent : baseEnd_2842166 < baseStart_2842166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842199 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 2, 3, 2]
def baseStart_2842199 : Nat := 118140960795 + 2842199 * 2 ^ 59
def prefixEnd_2842199 : Nat := 4983230072969 + 3 ^ 40 * 2842199 * 2
def baseEnd_2842199 : Nat := 1459414202728230617041471

theorem tailTrace_2842199 : CollatzResearch.WordTrace tailWord_2842199 prefixEnd_2842199 1459414202728230617041471 := by
  unfold tailWord_2842199
  simp only [CollatzResearch.WordTrace]
  refine ⟨103663513830205906788929651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69109009220137271192619767 103663513830205906788929651)
  ·
    refine ⟨155495270745308860183394477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103663513830205906788929651 155495270745308860183394477)
    ·
      refine ⟨58310726529490822568772929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155495270745308860183394477 58310726529490822568772929)
      ·
        refine ⟨43733044897118116926579697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58310726529490822568772929 43733044897118116926579697)
        ·
          refine ⟨32799783672838587694934773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43733044897118116926579697 32799783672838587694934773)
          ·
            refine ⟨3074979719328617596400135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32799783672838587694934773 3074979719328617596400135)
            ·
              refine ⟨4612469578992926394600203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3074979719328617596400135 4612469578992926394600203)
              ·
                refine ⟨6918704368489389591900305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4612469578992926394600203 6918704368489389591900305)
                ·
                  refine ⟨5189028276367042193925229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6918704368489389591900305 5189028276367042193925229)
                  ·
                    refine ⟨1945885603637640822721961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5189028276367042193925229 1945885603637640822721961)
                    ·
                      refine ⟨1459414202728230617041471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1945885603637640822721961 1459414202728230617041471)
                      ·
                        rfl

theorem cell23_2842199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_2842199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842199 prefixEnd_2842199 := by exact prefixLift 2842199
  have htrace : WordTrace (prefixWord ++ tailWord_2842199) baseStart_2842199 baseEnd_2842199 := by
    simpa [prefixWord, tailWord_2842199, baseEnd_2842199] using wordTrace_append hprefix tailTrace_2842199
  have hstable : (prefixWord ++ tailWord_2842199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842199).length < 2 ^ (prefixWord ++ tailWord_2842199).sum := by decide
  have hdescent : baseEnd_2842199 < baseStart_2842199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842208 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 6]
def baseStart_2842208 : Nat := 118140960795 + 2842208 * 2 ^ 59
def prefixEnd_2842208 : Nat := 4983230072969 + 3 ^ 40 * 2842208 * 2
def baseEnd_2842208 : Nat := 1459418824054121081828929

theorem tailTrace_2842208 : CollatzResearch.WordTrace tailWord_2842208 prefixEnd_2842208 1459418824054121081828929 := by
  unfold tailWord_2842208
  simp only [CollatzResearch.WordTrace]
  refine ⟨51831921043586650663003639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69109228058115534217338185 51831921043586650663003639)
  ·
    refine ⟨77747881565379975994505459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51831921043586650663003639 77747881565379975994505459)
    ·
      refine ⟨116621822348069963991758189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77747881565379975994505459 116621822348069963991758189)
      ·
        refine ⟨43733183380526236496909321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116621822348069963991758189 43733183380526236496909321)
        ·
          refine ⟨32799887535394677372681991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43733183380526236496909321 32799887535394677372681991)
          ·
            refine ⟨49199831303092016059022987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32799887535394677372681991 49199831303092016059022987)
            ·
              refine ⟨73799746954638024088534481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49199831303092016059022987 73799746954638024088534481)
              ·
                refine ⟨55349810215978518066400861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73799746954638024088534481 55349810215978518066400861)
                ·
                  refine ⟨20756178830991944274900323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55349810215978518066400861 20756178830991944274900323)
                  ·
                    refine ⟨31134268246487916412350485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20756178830991944274900323 31134268246487916412350485)
                    ·
                      refine ⟨1459418824054121081828929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31134268246487916412350485 1459418824054121081828929)
                      ·
                        rfl

theorem cell23_2842208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_2842208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842208 prefixEnd_2842208 := by exact prefixLift 2842208
  have htrace : WordTrace (prefixWord ++ tailWord_2842208) baseStart_2842208 baseEnd_2842208 := by
    simpa [prefixWord, tailWord_2842208, baseEnd_2842208] using wordTrace_append hprefix tailTrace_2842208
  have hstable : (prefixWord ++ tailWord_2842208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842208).length < 2 ^ (prefixWord ++ tailWord_2842208).sum := by decide
  have hdescent : baseEnd_2842208 < baseStart_2842208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842212 : List Nat := [2, 3, 1, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_2842212 : Nat := 118140960795 + 2842212 * 2 ^ 59
def prefixEnd_2842212 : Nat := 4983230072969 + 3 ^ 40 * 2842212 * 2
def baseEnd_2842212 : Nat := 1459420877976739066178911

theorem tailTrace_2842212 : CollatzResearch.WordTrace tailWord_2842212 prefixEnd_2842212 1459420877976739066178911 := by
  unfold tailWord_2842212
  simp only [CollatzResearch.WordTrace]
  refine ⟨51831993989579405004576445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69109325319439206672768593 51831993989579405004576445)
  ·
    refine ⟨19436997746092276876716167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51831993989579405004576445 19436997746092276876716167)
    ·
      refine ⟨29155496619138415315074251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19436997746092276876716167 29155496619138415315074251)
      ·
        refine ⟨43733244928707622972611377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29155496619138415315074251 43733244928707622972611377)
        ·
          refine ⟨32799933696530717229458533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43733244928707622972611377 32799933696530717229458533)
          ·
            refine ⟨6149987568099509480523475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32799933696530717229458533 6149987568099509480523475)
            ·
              refine ⟨9224981352149264220785213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6149987568099509480523475 9224981352149264220785213)
              ·
                refine ⟨3459368007055974082794455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9224981352149264220785213 3459368007055974082794455)
                ·
                  refine ⟨5189052010583961124191683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3459368007055974082794455 5189052010583961124191683)
                  ·
                    refine ⟨7783578015875941686287525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5189052010583961124191683 7783578015875941686287525)
                    ·
                      refine ⟨1459420877976739066178911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7783578015875941686287525 1459420877976739066178911)
                      ·
                        rfl

theorem cell23_2842212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_2842212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842212 prefixEnd_2842212 := by exact prefixLift 2842212
  have htrace : WordTrace (prefixWord ++ tailWord_2842212) baseStart_2842212 baseEnd_2842212 := by
    simpa [prefixWord, tailWord_2842212, baseEnd_2842212] using wordTrace_append hprefix tailTrace_2842212
  have hstable : (prefixWord ++ tailWord_2842212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842212).length < 2 ^ (prefixWord ++ tailWord_2842212).sum := by decide
  have hdescent : baseEnd_2842212 < baseStart_2842212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842263 : List Nat := [1, 1, 3, 3, 2, 4, 1, 3, 1, 2, 2]
def baseStart_2842263 : Nat := 118140960795 + 2842263 * 2 ^ 59
def prefixEnd_2842263 : Nat := 4983230072969 + 3 ^ 40 * 2842263 * 2
def baseEnd_2842263 : Nat := 1459447065490118366641177

theorem tailTrace_2842263 : CollatzResearch.WordTrace tailWord_2842263 prefixEnd_2842263 1459447065490118366641177 := by
  unfold tailWord_2842263
  simp only [CollatzResearch.WordTrace]
  refine ⟨103665848101974045719259443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69110565401316030479506295 103665848101974045719259443)
  ·
    refine ⟨155498772152961068578889165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103665848101974045719259443 155498772152961068578889165)
    ·
      refine ⟨58312039557360400717083437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155498772152961068578889165 58312039557360400717083437)
      ·
        refine ⟨21867014834010150268906289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58312039557360400717083437 21867014834010150268906289)
        ·
          refine ⟨16400261125507612701679717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21867014834010150268906289 16400261125507612701679717)
          ·
            refine ⟨3075048961032677381564947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16400261125507612701679717 3075048961032677381564947)
            ·
              refine ⟨4612573441549016072347421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3075048961032677381564947 4612573441549016072347421)
              ·
                refine ⟨1729715040580881027130283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4612573441549016072347421 1729715040580881027130283)
                ·
                  refine ⟨2594572560871321540695425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1729715040580881027130283 2594572560871321540695425)
                  ·
                    refine ⟨1945929420653491155521569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2594572560871321540695425 1945929420653491155521569)
                    ·
                      refine ⟨1459447065490118366641177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1945929420653491155521569 1459447065490118366641177)
                      ·
                        rfl

theorem cell23_2842263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_2842263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842263 prefixEnd_2842263 := by exact prefixLift 2842263
  have htrace : WordTrace (prefixWord ++ tailWord_2842263) baseStart_2842263 baseEnd_2842263 := by
    simpa [prefixWord, tailWord_2842263, baseEnd_2842263] using wordTrace_append hprefix tailTrace_2842263
  have hstable : (prefixWord ++ tailWord_2842263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842263).length < 2 ^ (prefixWord ++ tailWord_2842263).sum := by decide
  have hdescent : baseEnd_2842263 < baseStart_2842263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842322 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2842322 : Nat := 118140960795 + 2842322 * 2 ^ 59
def prefixEnd_2842322 : Nat := 4983230072969 + 3 ^ 40 * 2842322 * 2
def baseEnd_2842322 : Nat := 1459477360848733635803405

theorem tailTrace_2842322 : CollatzResearch.WordTrace tailWord_2842322 prefixEnd_2842322 1459477360848733635803405 := by
  unfold tailWord_2842322
  simp only [CollatzResearch.WordTrace]
  refine ⟨25917000002190074698914305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69112000005840199197104813 25917000002190074698914305)
  ·
    refine ⟨19437750001642556024185729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25917000002190074698914305 19437750001642556024185729)
    ·
      refine ⟨14578312501231917018139297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19437750001642556024185729 14578312501231917018139297)
      ·
        refine ⟨10933734375923937763604473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14578312501231917018139297 10933734375923937763604473)
        ·
          refine ⟨8200300781942953322703355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10933734375923937763604473 8200300781942953322703355)
          ·
            refine ⟨12300451172914429984055033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8200300781942953322703355 12300451172914429984055033)
            ·
              refine ⟨9225338379685822488041275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12300451172914429984055033 9225338379685822488041275)
              ·
                refine ⟨13838007569528733732061913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9225338379685822488041275 13838007569528733732061913)
                ·
                  refine ⟨10378505677146550299046435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13838007569528733732061913 10378505677146550299046435)
                  ·
                    refine ⟨15567758515719825448569653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10378505677146550299046435 15567758515719825448569653)
                    ·
                      refine ⟨1459477360848733635803405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15567758515719825448569653 1459477360848733635803405)
                      ·
                        rfl

theorem cell23_2842322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2842322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842322 prefixEnd_2842322 := by exact prefixLift 2842322
  have htrace : WordTrace (prefixWord ++ tailWord_2842322) baseStart_2842322 baseEnd_2842322 := by
    simpa [prefixWord, tailWord_2842322, baseEnd_2842322] using wordTrace_append hprefix tailTrace_2842322
  have hstable : (prefixWord ++ tailWord_2842322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842322).length < 2 ^ (prefixWord ++ tailWord_2842322).sum := by decide
  have hdescent : baseEnd_2842322 < baseStart_2842322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842355 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 4, 5]
def baseStart_2842355 : Nat := 118140960795 + 2842355 * 2 ^ 59
def prefixEnd_2842355 : Nat := 4983230072969 + 3 ^ 40 * 2842355 * 2
def baseEnd_2842355 : Nat := 486498101903444002230251

theorem tailTrace_2842355 : CollatzResearch.WordTrace tailWord_2842355 prefixEnd_2842355 486498101903444002230251 := by
  unfold tailWord_2842355
  simp only [CollatzResearch.WordTrace]
  refine ⟨103669203617640745431608519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69112802411760496954405679 103669203617640745431608519)
  ·
    refine ⟨155503805426461118147412779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103669203617640745431608519 155503805426461118147412779)
    ·
      refine ⟨233255708139691677221119169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155503805426461118147412779 233255708139691677221119169)
      ·
        refine ⟨174941781104768757915839377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233255708139691677221119169 174941781104768757915839377)
        ·
          refine ⟨131206335828576568436879533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174941781104768757915839377 131206335828576568436879533)
          ·
            refine ⟨49202375935716213163829825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131206335828576568436879533 49202375935716213163829825)
            ·
              refine ⟨36901781951787159872872369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49202375935716213163829825 36901781951787159872872369)
              ·
                refine ⟨27676336463840369904654277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36901781951787159872872369 27676336463840369904654277)
                ·
                  refine ⟨5189313086970069357122677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27676336463840369904654277 5189313086970069357122677)
                  ·
                    refine ⟨486498101903444002230251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5189313086970069357122677 486498101903444002230251)
                    ·
                      rfl

theorem cell23_2842355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 5].length) (baseStart_2842355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842355 prefixEnd_2842355 := by exact prefixLift 2842355
  have htrace : WordTrace (prefixWord ++ tailWord_2842355) baseStart_2842355 baseEnd_2842355 := by
    simpa [prefixWord, tailWord_2842355, baseEnd_2842355] using wordTrace_append hprefix tailTrace_2842355
  have hstable : (prefixWord ++ tailWord_2842355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842355).length < 2 ^ (prefixWord ++ tailWord_2842355).sum := by decide
  have hdescent : baseEnd_2842355 < baseStart_2842355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842362 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2]
def baseStart_2842362 : Nat := 118140960795 + 2842362 * 2 ^ 59
def prefixEnd_2842362 : Nat := 4983230072969 + 3 ^ 40 * 2842362 * 2
def baseEnd_2842362 : Nat := 1459497900074913479303221

theorem tailTrace_2842362 : CollatzResearch.WordTrace tailWord_2842362 prefixEnd_2842362 1459497900074913479303221 := by
  unfold tailWord_2842362
  simp only [CollatzResearch.WordTrace]
  refine ⟨25917364732153846406778335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69112972619076923751408893 25917364732153846406778335)
  ·
    refine ⟨38876047098230769610167503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25917364732153846406778335 38876047098230769610167503)
    ·
      refine ⟨58314070647346154415251255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38876047098230769610167503 58314070647346154415251255)
      ·
        refine ⟨87471105971019231622876883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58314070647346154415251255 87471105971019231622876883)
        ·
          refine ⟨131206658956528847434315325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87471105971019231622876883 131206658956528847434315325)
          ·
            refine ⟨49202497108698317787868247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131206658956528847434315325 49202497108698317787868247)
            ·
              refine ⟨73803745663047476681802371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49202497108698317787868247 73803745663047476681802371)
              ·
                refine ⟨110705618494571215022703557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73803745663047476681802371 110705618494571215022703557)
                ·
                  refine ⟨20757303467732102816756917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110705618494571215022703557 20757303467732102816756917)
                  ·
                    refine ⟨1945997200099884639070961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20757303467732102816756917 1945997200099884639070961)
                    ·
                      refine ⟨1459497900074913479303221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1945997200099884639070961 1459497900074913479303221)
                      ·
                        rfl

theorem cell23_2842362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2].length) (baseStart_2842362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842362 prefixEnd_2842362 := by exact prefixLift 2842362
  have htrace : WordTrace (prefixWord ++ tailWord_2842362) baseStart_2842362 baseEnd_2842362 := by
    simpa [prefixWord, tailWord_2842362, baseEnd_2842362] using wordTrace_append hprefix tailTrace_2842362
  have hstable : (prefixWord ++ tailWord_2842362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842362).length < 2 ^ (prefixWord ++ tailWord_2842362).sum := by decide
  have hdescent : baseEnd_2842362 < baseStart_2842362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842365 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_2842365 : Nat := 118140960795 + 2842365 * 2 ^ 59
def prefixEnd_2842365 : Nat := 4983230072969 + 3 ^ 40 * 2842365 * 2
def baseEnd_2842365 : Nat := 1459499440516876967565707

theorem tailTrace_2842365 : CollatzResearch.WordTrace tailWord_2842365 prefixEnd_2842365 1459499440516876967565707 := by
  unfold tailWord_2842365
  simp only [CollatzResearch.WordTrace]
  refine ⟨103669568347604517139472549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69113045565069678092981699 103669568347604517139472549)
  ·
    refine ⟨19438044065175846963651103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103669568347604517139472549 19438044065175846963651103)
    ·
      refine ⟨29157066097763770445476655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19438044065175846963651103 29157066097763770445476655)
      ·
        refine ⟨43735599146645655668214983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29157066097763770445476655 43735599146645655668214983)
        ·
          refine ⟨65603398719968483502322475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43735599146645655668214983 65603398719968483502322475)
          ·
            refine ⟨98405098079952725253483713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65603398719968483502322475 98405098079952725253483713)
            ·
              refine ⟨73803823559964543940112785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98405098079952725253483713 73803823559964543940112785)
              ·
                refine ⟨55352867669973407955084589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73803823559964543940112785 55352867669973407955084589)
                ·
                  refine ⟨20757325376240027983156721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55352867669973407955084589 20757325376240027983156721)
                  ·
                    refine ⟨15567994032180020987367541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20757325376240027983156721 15567994032180020987367541)
                    ·
                      refine ⟨1459499440516876967565707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15567994032180020987367541 1459499440516876967565707)
                      ·
                        rfl

theorem cell23_2842365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_2842365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842365 prefixEnd_2842365 := by exact prefixLift 2842365
  have htrace : WordTrace (prefixWord ++ tailWord_2842365) baseStart_2842365 baseEnd_2842365 := by
    simpa [prefixWord, tailWord_2842365, baseEnd_2842365] using wordTrace_append hprefix tailTrace_2842365
  have hstable : (prefixWord ++ tailWord_2842365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842365).length < 2 ^ (prefixWord ++ tailWord_2842365).sum := by decide
  have hdescent : baseEnd_2842365 < baseStart_2842365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842372 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_2842372 : Nat := 118140960795 + 2842372 * 2 ^ 59
def prefixEnd_2842372 : Nat := 4983230072969 + 3 ^ 40 * 2842372 * 2
def baseEnd_2842372 : Nat := 486501011627152813392725

theorem tailTrace_2842372 : CollatzResearch.WordTrace tailWord_2842372 prefixEnd_2842372 486501011627152813392725 := by
  unfold tailWord_2842372
  simp only [CollatzResearch.WordTrace]
  refine ⟨51834911829289578667488685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69113215772386104889984913 51834911829289578667488685)
  ·
    refine ⟨19438091935983592000308257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51834911829289578667488685 19438091935983592000308257)
    ·
      refine ⟨14578568951987694000231193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19438091935983592000308257 14578568951987694000231193)
      ·
        refine ⟨10933926713990770500173395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14578568951987694000231193 10933926713990770500173395)
        ·
          refine ⟨16400890070986155750260093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10933926713990770500173395 16400890070986155750260093)
          ·
            refine ⟨6150333776619808406347535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16400890070986155750260093 6150333776619808406347535)
            ·
              refine ⟨9225500664929712609521303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6150333776619808406347535 9225500664929712609521303)
              ·
                refine ⟨13838250997394568914281955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9225500664929712609521303 13838250997394568914281955)
                ·
                  refine ⟨20757376496091853371422933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13838250997394568914281955 20757376496091853371422933)
                  ·
                    refine ⟨486501011627152813392725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20757376496091853371422933 486501011627152813392725)
                    ·
                      rfl

theorem cell23_2842372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_2842372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842372 prefixEnd_2842372 := by exact prefixLift 2842372
  have htrace : WordTrace (prefixWord ++ tailWord_2842372) baseStart_2842372 baseEnd_2842372 := by
    simpa [prefixWord, tailWord_2842372, baseEnd_2842372] using wordTrace_append hprefix tailTrace_2842372
  have hstable : (prefixWord ++ tailWord_2842372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842372).length < 2 ^ (prefixWord ++ tailWord_2842372).sum := by decide
  have hdescent : baseEnd_2842372 < baseStart_2842372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842374 : List Nat := [6, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2842374 : Nat := 118140960795 + 2842374 * 2 ^ 59
def prefixEnd_2842374 : Nat := 4983230072969 + 3 ^ 40 * 2842374 * 2
def baseEnd_2842374 : Nat := 1459504061842767432353167

theorem tailTrace_2842374 : CollatzResearch.WordTrace tailWord_2842374 prefixEnd_2842374 1459504061842767432353167 := by
  unfold tailWord_2842374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3239684268892872239892193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69113264403047941117700117 3239684268892872239892193)
  ·
    refine ⟨2429763201669654179919145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3239684268892872239892193 2429763201669654179919145)
    ·
      refine ⟨1822322401252240634939359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2429763201669654179919145 1822322401252240634939359)
      ·
        refine ⟨2733483601878360952409039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1822322401252240634939359 2733483601878360952409039)
        ·
          refine ⟨4100225402817541428613559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2733483601878360952409039 4100225402817541428613559)
          ·
            refine ⟨6150338104226312142920339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4100225402817541428613559 6150338104226312142920339)
            ·
              refine ⟨9225507156339468214380509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6150338104226312142920339 9225507156339468214380509)
              ·
                refine ⟨3459565183627300580392691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9225507156339468214380509 3459565183627300580392691)
                ·
                  refine ⟨5189347775440950870589037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3459565183627300580392691 5189347775440950870589037)
                  ·
                    refine ⟨1946005415790356576470889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5189347775440950870589037 1946005415790356576470889)
                    ·
                      refine ⟨1459504061842767432353167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1946005415790356576470889 1459504061842767432353167)
                      ·
                        rfl

theorem cell23_2842374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2842374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842374 prefixEnd_2842374 := by exact prefixLift 2842374
  have htrace : WordTrace (prefixWord ++ tailWord_2842374) baseStart_2842374 baseEnd_2842374 := by
    simpa [prefixWord, tailWord_2842374, baseEnd_2842374] using wordTrace_append hprefix tailTrace_2842374
  have hstable : (prefixWord ++ tailWord_2842374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842374).length < 2 ^ (prefixWord ++ tailWord_2842374).sum := by decide
  have hdescent : baseEnd_2842374 < baseStart_2842374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842392 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_2842392 : Nat := 118140960795 + 2842392 * 2 ^ 59
def prefixEnd_2842392 : Nat := 4983230072969 + 3 ^ 40 * 2842392 * 2
def baseEnd_2842392 : Nat := 1459513304494548361928083

theorem tailTrace_2842392 : CollatzResearch.WordTrace tailWord_2842392 prefixEnd_2842392 1459513304494548361928083 := by
  unfold tailWord_2842392
  simp only [CollatzResearch.WordTrace]
  refine ⟨51835276559253350375352715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69113702079004467167136953 51835276559253350375352715)
  ·
    refine ⟨77752914838880025563029073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51835276559253350375352715 77752914838880025563029073)
    ·
      refine ⟨58314686129160019172271805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77752914838880025563029073 58314686129160019172271805)
      ·
        refine ⟨21868007298435007189601927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58314686129160019172271805 21868007298435007189601927)
        ·
          refine ⟨32802010947652510784402891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21868007298435007189601927 32802010947652510784402891)
          ·
            refine ⟨49203016421478766176604337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32802010947652510784402891 49203016421478766176604337)
            ·
              refine ⟨36902262316109074632453253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49203016421478766176604337 36902262316109074632453253)
              ·
                refine ⟨6919174184270451493584985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36902262316109074632453253 6919174184270451493584985)
                ·
                  refine ⟨5189380638202838620188739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6919174184270451493584985 5189380638202838620188739)
                  ·
                    refine ⟨7784070957304257930283109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5189380638202838620188739 7784070957304257930283109)
                    ·
                      refine ⟨1459513304494548361928083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7784070957304257930283109 1459513304494548361928083)
                      ·
                        rfl

theorem cell23_2842392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_2842392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842392 prefixEnd_2842392 := by exact prefixLift 2842392
  have htrace : WordTrace (prefixWord ++ tailWord_2842392) baseStart_2842392 baseEnd_2842392 := by
    simpa [prefixWord, tailWord_2842392, baseEnd_2842392] using wordTrace_append hprefix tailTrace_2842392
  have hstable : (prefixWord ++ tailWord_2842392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842392).length < 2 ^ (prefixWord ++ tailWord_2842392).sum := by decide
  have hdescent : baseEnd_2842392 < baseStart_2842392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842412 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 3]
def baseStart_2842412 : Nat := 118140960795 + 2842412 * 2 ^ 59
def prefixEnd_2842412 : Nat := 4983230072969 + 3 ^ 40 * 2842412 * 2
def baseEnd_2842412 : Nat := 1459523574107638283677991

theorem tailTrace_2842412 : CollatzResearch.WordTrace tailWord_2842412 prefixEnd_2842412 1459523574107638283677991 := by
  unfold tailWord_2842412
  simp only [CollatzResearch.WordTrace]
  refine ⟨51835641289217122083216745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69114188385622829444288993 51835641289217122083216745)
  ·
    refine ⟨38876730966912841562412559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51835641289217122083216745 38876730966912841562412559)
    ·
      refine ⟨58315096450369262343618839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38876730966912841562412559 58315096450369262343618839)
      ·
        refine ⟨87472644675553893515428259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58315096450369262343618839 87472644675553893515428259)
        ·
          refine ⟨131208967013330840273142389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87472644675553893515428259 131208967013330840273142389)
          ·
            refine ⟨12300840657499766275607099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131208967013330840273142389 12300840657499766275607099)
            ·
              refine ⟨18451260986249649413410649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12300840657499766275607099 18451260986249649413410649)
              ·
                refine ⟨13838445739687237060057987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18451260986249649413410649 13838445739687237060057987)
                ·
                  refine ⟨20757668609530855590086981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13838445739687237060057987 20757668609530855590086981)
                  ·
                    refine ⟨3892062864287035423141309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20757668609530855590086981 3892062864287035423141309)
                    ·
                      refine ⟨1459523574107638283677991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3892062864287035423141309 1459523574107638283677991)
                      ·
                        rfl

theorem cell23_2842412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_2842412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842412 prefixEnd_2842412 := by exact prefixLift 2842412
  have htrace : WordTrace (prefixWord ++ tailWord_2842412) baseStart_2842412 baseEnd_2842412 := by
    simpa [prefixWord, tailWord_2842412, baseEnd_2842412] using wordTrace_append hprefix tailTrace_2842412
  have hstable : (prefixWord ++ tailWord_2842412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842412).length < 2 ^ (prefixWord ++ tailWord_2842412).sum := by decide
  have hdescent : baseEnd_2842412 < baseStart_2842412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842429 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2842429 : Nat := 118140960795 + 2842429 * 2 ^ 59
def prefixEnd_2842429 : Nat := 4983230072969 + 3 ^ 40 * 2842429 * 2
def baseEnd_2842429 : Nat := 1459532303278764717165413

theorem tailTrace_2842429 : CollatzResearch.WordTrace tailWord_2842429 prefixEnd_2842429 1459532303278764717165413 := by
  unfold tailWord_2842429
  simp only [CollatzResearch.WordTrace]
  refine ⟨103671902619372656069802341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69114601746248437379868227 103671902619372656069802341)
  ·
    refine ⟨19438481741132373013087939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103671902619372656069802341 19438481741132373013087939)
    ·
      refine ⟨29157722611698559519631909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19438481741132373013087939 29157722611698559519631909)
      ·
        refine ⟨5467072989693479909930983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29157722611698559519631909 5467072989693479909930983)
        ·
          refine ⟨8200609484540219864896475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5467072989693479909930983 8200609484540219864896475)
          ·
            refine ⟨12300914226810329797344713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8200609484540219864896475 12300914226810329797344713)
            ·
              refine ⟨9225685670107747348008535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12300914226810329797344713 9225685670107747348008535)
              ·
                refine ⟨13838528505161621022012803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9225685670107747348008535 13838528505161621022012803)
                ·
                  refine ⟨20757792757742431533019205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13838528505161621022012803 20757792757742431533019205)
                  ·
                    refine ⟨3892086142076705912441101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20757792757742431533019205 3892086142076705912441101)
                    ·
                      refine ⟨1459532303278764717165413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3892086142076705912441101 1459532303278764717165413)
                      ·
                        rfl

theorem cell23_2842429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2842429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842429 prefixEnd_2842429 := by exact prefixLift 2842429
  have htrace : WordTrace (prefixWord ++ tailWord_2842429) baseStart_2842429 baseEnd_2842429 := by
    simpa [prefixWord, tailWord_2842429, baseEnd_2842429] using wordTrace_append hprefix tailTrace_2842429
  have hstable : (prefixWord ++ tailWord_2842429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842429).length < 2 ^ (prefixWord ++ tailWord_2842429).sum := by decide
  have hdescent : baseEnd_2842429 < baseStart_2842429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842453 : List Nat := [1, 3, 2, 2, 2, 3, 3, 2, 1, 4]
def baseStart_2842453 : Nat := 118140960795 + 2842453 * 2 ^ 59
def prefixEnd_2842453 : Nat := 4983230072969 + 3 ^ 40 * 2842453 * 2
def baseEnd_2842453 : Nat := 486514875604824207755101

theorem tailTrace_2842453 : CollatzResearch.WordTrace tailWord_2842453 prefixEnd_2842453 486514875604824207755101 := by
  unfold tailWord_2842453
  simp only [CollatzResearch.WordTrace]
  refine ⟨103672777971285708168676013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69115185314190472112450675 103672777971285708168676013)
  ·
    refine ⟨38877291739232140563253505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103672777971285708168676013 38877291739232140563253505)
    ·
      refine ⟨29157968804424105422440129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38877291739232140563253505 29157968804424105422440129)
      ·
        refine ⟨21868476603318079066830097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29157968804424105422440129 21868476603318079066830097)
        ·
          refine ⟨16401357452488559300122573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21868476603318079066830097 16401357452488559300122573)
          ·
            refine ⟨6150509044683209737545965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16401357452488559300122573 6150509044683209737545965)
            ·
              refine ⟨2306440891756203651579737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6150509044683209737545965 2306440891756203651579737)
              ·
                refine ⟨1729830668817152738684803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2306440891756203651579737 1729830668817152738684803)
                ·
                  refine ⟨2594746003225729108027205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1729830668817152738684803 2594746003225729108027205)
                  ·
                    refine ⟨486514875604824207755101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2594746003225729108027205 486514875604824207755101)
                    ·
                      rfl

theorem cell23_2842453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_2842453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842453 prefixEnd_2842453 := by exact prefixLift 2842453
  have htrace : WordTrace (prefixWord ++ tailWord_2842453) baseStart_2842453 baseEnd_2842453 := by
    simpa [prefixWord, tailWord_2842453, baseEnd_2842453] using wordTrace_append hprefix tailTrace_2842453
  have hstable : (prefixWord ++ tailWord_2842453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842453).length < 2 ^ (prefixWord ++ tailWord_2842453).sum := by decide
  have hdescent : baseEnd_2842453 < baseStart_2842453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842466 : List Nat := [3, 3, 2, 1, 2, 1, 4, 1, 6]
def baseStart_2842466 : Nat := 118140960795 + 2842466 * 2 ^ 59
def prefixEnd_2842466 : Nat := 4983230072969 + 3 ^ 40 * 2842466 * 2
def baseEnd_2842466 : Nat := 162172366895886785822527

theorem tailTrace_2842466 : CollatzResearch.WordTrace tailWord_2842466 prefixEnd_2842466 162172366895886785822527 := by
  unfold tailWord_2842466
  simp only [CollatzResearch.WordTrace]
  refine ⟨25918313030059652847224813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69115501413492407592599501 25918313030059652847224813)
  ·
    refine ⟨9719367386272369817709305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25918313030059652847224813 9719367386272369817709305)
    ·
      refine ⟨7289525539704277363281979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9719367386272369817709305 7289525539704277363281979)
      ·
        refine ⟨10934288309556416044922969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7289525539704277363281979 10934288309556416044922969)
        ·
          refine ⟨8200716232167312033692227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10934288309556416044922969 8200716232167312033692227)
          ·
            refine ⟨12301074348250968050538341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8200716232167312033692227 12301074348250968050538341)
            ·
              refine ⟨2306451440297056509475939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12301074348250968050538341 2306451440297056509475939)
              ·
                refine ⟨3459677160445584764213909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2306451440297056509475939 3459677160445584764213909)
                ·
                  refine ⟨162172366895886785822527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3459677160445584764213909 162172366895886785822527)
                  ·
                    rfl

theorem cell23_2842466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_2842466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842466 prefixEnd_2842466 := by exact prefixLift 2842466
  have htrace : WordTrace (prefixWord ++ tailWord_2842466) baseStart_2842466 baseEnd_2842466 := by
    simpa [prefixWord, tailWord_2842466, baseEnd_2842466] using wordTrace_append hprefix tailTrace_2842466
  have hstable : (prefixWord ++ tailWord_2842466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842466).length < 2 ^ (prefixWord ++ tailWord_2842466).sum := by decide
  have hdescent : baseEnd_2842466 < baseStart_2842466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842469 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 6, 3, 2]
def baseStart_2842469 : Nat := 118140960795 + 2842469 * 2 ^ 59
def prefixEnd_2842469 : Nat := 4983230072969 + 3 ^ 40 * 2842469 * 2
def baseEnd_2842469 : Nat := 1459552842504944560665229

theorem tailTrace_2842469 : CollatzResearch.WordTrace tailWord_2842469 prefixEnd_2842469 1459552842504944560665229 := by
  unfold tailWord_2842469
  simp only [CollatzResearch.WordTrace]
  refine ⟨103673361539227742901258461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69115574359485161934172307 103673361539227742901258461)
  ·
    refine ⟨38877510577210403587971923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103673361539227742901258461 38877510577210403587971923)
    ·
      refine ⟨58316265865815605381957885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38877510577210403587971923 58316265865815605381957885)
      ·
        refine ⟨21868599699680852018234207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58316265865815605381957885 21868599699680852018234207)
        ·
          refine ⟨32802899549521278027351311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21868599699680852018234207 32802899549521278027351311)
          ·
            refine ⟨49204349324281917041026967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32802899549521278027351311 49204349324281917041026967)
            ·
              refine ⟨73806523986422875561540451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49204349324281917041026967 73806523986422875561540451)
              ·
                refine ⟨110709785979634313342310677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73806523986422875561540451 110709785979634313342310677)
                ·
                  refine ⟨5189521217795358437920813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110709785979634313342310677 5189521217795358437920813)
                  ·
                    refine ⟨1946070456673259414220305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5189521217795358437920813 1946070456673259414220305)
                    ·
                      refine ⟨1459552842504944560665229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1946070456673259414220305 1459552842504944560665229)
                      ·
                        rfl

theorem cell23_2842469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_2842469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842469 prefixEnd_2842469 := by exact prefixLift 2842469
  have htrace : WordTrace (prefixWord ++ tailWord_2842469) baseStart_2842469 baseEnd_2842469 := by
    simpa [prefixWord, tailWord_2842469, baseEnd_2842469] using wordTrace_append hprefix tailTrace_2842469
  have hstable : (prefixWord ++ tailWord_2842469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842469).length < 2 ^ (prefixWord ++ tailWord_2842469).sum := by decide
  have hdescent : baseEnd_2842469 < baseStart_2842469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842519 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 3]
def baseStart_2842519 : Nat := 118140960795 + 2842519 * 2 ^ 59
def prefixEnd_2842519 : Nat := 4983230072969 + 3 ^ 40 * 2842519 * 2
def baseEnd_2842519 : Nat := 1459578516537669365039999

theorem tailTrace_2842519 : CollatzResearch.WordTrace tailWord_2842519 prefixEnd_2842519 1459578516537669365039999 := by
  unfold tailWord_2842519
  simp only [CollatzResearch.WordTrace]
  refine ⟨103675185189046601440578611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69116790126031067627052407 103675185189046601440578611)
  ·
    refine ⟨155512777783569902160867917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103675185189046601440578611 155512777783569902160867917)
    ·
      refine ⟨58317291668838713310325469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155512777783569902160867917 58317291668838713310325469)
      ·
        refine ⟨21868984375814517491372051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58317291668838713310325469 21868984375814517491372051)
        ·
          refine ⟨32803476563721776237058077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21868984375814517491372051 32803476563721776237058077)
          ·
            refine ⟨12301303711395666088896779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32803476563721776237058077 12301303711395666088896779)
            ·
              refine ⟨18451955567093499133345169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12301303711395666088896779 18451955567093499133345169)
              ·
                refine ⟨13838966675320124350008877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18451955567093499133345169 13838966675320124350008877)
                ·
                  refine ⟨5189612503245046631253329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13838966675320124350008877 5189612503245046631253329)
                  ·
                    refine ⟨3892209377433784973439997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5189612503245046631253329 3892209377433784973439997)
                    ·
                      refine ⟨1459578516537669365039999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3892209377433784973439997 1459578516537669365039999)
                      ·
                        rfl

theorem cell23_2842519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_2842519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842519 prefixEnd_2842519 := by exact prefixLift 2842519
  have htrace : WordTrace (prefixWord ++ tailWord_2842519) baseStart_2842519 baseEnd_2842519 := by
    simpa [prefixWord, tailWord_2842519, baseEnd_2842519] using wordTrace_append hprefix tailTrace_2842519
  have hstable : (prefixWord ++ tailWord_2842519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842519).length < 2 ^ (prefixWord ++ tailWord_2842519).sum := by decide
  have hdescent : baseEnd_2842519 < baseStart_2842519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842583 : List Nat := [1, 1, 3, 2, 1, 1, 7, 1, 2, 1, 3]
def baseStart_2842583 : Nat := 118140960795 + 2842583 * 2 ^ 59
def prefixEnd_2842583 : Nat := 4983230072969 + 3 ^ 40 * 2842583 * 2
def baseEnd_2842583 : Nat := 1459611379299557114639705

theorem tailTrace_2842583 : CollatzResearch.WordTrace tailWord_2842583 prefixEnd_2842583 1459611379299557114639705 := by
  unfold tailWord_2842583
  simp only [CollatzResearch.WordTrace]
  refine ⟨103677519460814740370908403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69118346307209826913938935 103677519460814740370908403)
  ·
    refine ⟨155516279191222110556362605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103677519460814740370908403 155516279191222110556362605)
    ·
      refine ⟨58318604696708291458635977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155516279191222110556362605 58318604696708291458635977)
      ·
        refine ⟨43738953522531218593976983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58318604696708291458635977 43738953522531218593976983)
        ·
          refine ⟨65608430283796827890965475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43738953522531218593976983 65608430283796827890965475)
          ·
            refine ⟨98412645425695241836448213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65608430283796827890965475 98412645425695241836448213)
            ·
              refine ⟨2306546377164732230541755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 98412645425695241836448213 2306546377164732230541755)
              ·
                refine ⟨3459819565747098345812633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2306546377164732230541755 3459819565747098345812633)
                ·
                  refine ⟨2594864674310323759359475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3459819565747098345812633 2594864674310323759359475)
                  ·
                    refine ⟨3892297011465485639039213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2594864674310323759359475 3892297011465485639039213)
                    ·
                      refine ⟨1459611379299557114639705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3892297011465485639039213 1459611379299557114639705)
                      ·
                        rfl

theorem cell23_2842583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_2842583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842583 prefixEnd_2842583 := by exact prefixLift 2842583
  have htrace : WordTrace (prefixWord ++ tailWord_2842583) baseStart_2842583 baseEnd_2842583 := by
    simpa [prefixWord, tailWord_2842583, baseEnd_2842583] using wordTrace_append hprefix tailTrace_2842583
  have hstable : (prefixWord ++ tailWord_2842583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842583).length < 2 ^ (prefixWord ++ tailWord_2842583).sum := by decide
  have hdescent : baseEnd_2842583 < baseStart_2842583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842592 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 5]
def baseStart_2842592 : Nat := 118140960795 + 2842592 * 2 ^ 59
def prefixEnd_2842592 : Nat := 4983230072969 + 3 ^ 40 * 2842592 * 2
def baseEnd_2842592 : Nat := 1459616000625447579427163

theorem tailTrace_2842592 : CollatzResearch.WordTrace tailWord_2842592 prefixEnd_2842592 1459616000625447579427163 := by
  unfold tailWord_2842592
  simp only [CollatzResearch.WordTrace]
  refine ⟨51838923858891067453993015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69118565145188089938657353 51838923858891067453993015)
  ·
    refine ⟨77758385788336601180989523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51838923858891067453993015 77758385788336601180989523)
    ·
      refine ⟨116637578682504901771484285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77758385788336601180989523 116637578682504901771484285)
      ·
        refine ⟨43739092005939338164306607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116637578682504901771484285 43739092005939338164306607)
        ·
          refine ⟨65608638008909007246459911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43739092005939338164306607 65608638008909007246459911)
          ·
            refine ⟨98412957013363510869689867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65608638008909007246459911 98412957013363510869689867)
            ·
              refine ⟨147619435520045266304534801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98412957013363510869689867 147619435520045266304534801)
              ·
                refine ⟨110714576640033949728401101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147619435520045266304534801 110714576640033949728401101)
                ·
                  refine ⟨41517966240012731148150413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110714576640033949728401101 41517966240012731148150413)
                  ·
                    refine ⟨15569237340004774180556405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41517966240012731148150413 15569237340004774180556405)
                    ·
                      refine ⟨1459616000625447579427163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15569237340004774180556405 1459616000625447579427163)
                      ·
                        rfl

theorem cell23_2842592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_2842592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842592 prefixEnd_2842592 := by exact prefixLift 2842592
  have htrace : WordTrace (prefixWord ++ tailWord_2842592) baseStart_2842592 baseEnd_2842592 := by
    simpa [prefixWord, tailWord_2842592, baseEnd_2842592] using wordTrace_append hprefix tailTrace_2842592
  have hstable : (prefixWord ++ tailWord_2842592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842592).length < 2 ^ (prefixWord ++ tailWord_2842592).sum := by decide
  have hdescent : baseEnd_2842592 < baseStart_2842592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842629 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 7]
def baseStart_2842629 : Nat := 118140960795 + 2842629 * 2 ^ 59
def prefixEnd_2842629 : Nat := 4983230072969 + 3 ^ 40 * 2842629 * 2
def baseEnd_2842629 : Nat := 162181666601073770518277

theorem tailTrace_2842629 : CollatzResearch.WordTrace tailWord_2842629 prefixEnd_2842629 162181666601073770518277 := by
  unfold tailWord_2842629
  simp only [CollatzResearch.WordTrace]
  refine ⟨103679197218648090227082941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69119464812432060151388627 103679197218648090227082941)
  ·
    refine ⟨38879698956993033835156103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103679197218648090227082941 38879698956993033835156103)
    ·
      refine ⟨58319548435489550752734155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38879698956993033835156103 58319548435489550752734155)
      ·
        refine ⟨87479322653234326129101233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58319548435489550752734155 87479322653234326129101233)
        ·
          refine ⟨65609491989925744596825925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87479322653234326129101233 65609491989925744596825925)
          ·
            refine ⟨12301779748111077111904861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65609491989925744596825925 12301779748111077111904861)
            ·
              refine ⟨4613167405541653916964323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12301779748111077111904861 4613167405541653916964323)
              ·
                refine ⟨6919751108312480875446485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4613167405541653916964323 6919751108312480875446485)
                ·
                  refine ⟨162181666601073770518277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6919751108312480875446485 162181666601073770518277)
                  ·
                    rfl

theorem cell23_2842629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_2842629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842629 prefixEnd_2842629 := by exact prefixLift 2842629
  have htrace : WordTrace (prefixWord ++ tailWord_2842629) baseStart_2842629 baseEnd_2842629 := by
    simpa [prefixWord, tailWord_2842629, baseEnd_2842629] using wordTrace_append hprefix tailTrace_2842629
  have hstable : (prefixWord ++ tailWord_2842629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842629).length < 2 ^ (prefixWord ++ tailWord_2842629).sum := by decide
  have hdescent : baseEnd_2842629 < baseStart_2842629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842644 : List Nat := [2, 4, 3, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_2842644 : Nat := 118140960795 + 2842644 * 2 ^ 59
def prefixEnd_2842644 : Nat := 4983230072969 + 3 ^ 40 * 2842644 * 2
def baseEnd_2842644 : Nat := 1459642701619481375976925

theorem tailTrace_2842644 : CollatzResearch.WordTrace tailWord_2842644 prefixEnd_2842644 1459642701619481375976925 := by
  unfold tailWord_2842644
  simp only [CollatzResearch.WordTrace]
  refine ⟨51839872156796873894439493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69119829542395831859252657 51839872156796873894439493)
  ·
    refine ⟨9719976029399413855207405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51839872156796873894439493 9719976029399413855207405)
    ·
      refine ⟨3644991011024780195702777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9719976029399413855207405 3644991011024780195702777)
      ·
        refine ⟨2733743258268585146777083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3644991011024780195702777 2733743258268585146777083)
        ·
          refine ⟨4100614887402877720165625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2733743258268585146777083 4100614887402877720165625)
          ·
            refine ⟨3075461165552158290124219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4100614887402877720165625 3075461165552158290124219)
            ·
              refine ⟨4613191748328237435186329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3075461165552158290124219 4613191748328237435186329)
              ·
                refine ⟨3459893811246178076389747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4613191748328237435186329 3459893811246178076389747)
                ·
                  refine ⟨5189840716869267114584621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3459893811246178076389747 5189840716869267114584621)
                  ·
                    refine ⟨1946190268825975167969233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5189840716869267114584621 1946190268825975167969233)
                    ·
                      refine ⟨1459642701619481375976925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1946190268825975167969233 1459642701619481375976925)
                      ·
                        rfl

theorem cell23_2842644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_2842644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842644 prefixEnd_2842644 := by exact prefixLift 2842644
  have htrace : WordTrace (prefixWord ++ tailWord_2842644) baseStart_2842644 baseEnd_2842644 := by
    simpa [prefixWord, tailWord_2842644, baseEnd_2842644] using wordTrace_append hprefix tailTrace_2842644
  have hstable : (prefixWord ++ tailWord_2842644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842644).length < 2 ^ (prefixWord ++ tailWord_2842644).sum := by decide
  have hdescent : baseEnd_2842644 < baseStart_2842644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842680 : List Nat := [2, 1, 2, 1, 6, 2, 2, 2, 5]
def baseStart_2842680 : Nat := 118140960795 + 2842680 * 2 ^ 59
def prefixEnd_2842680 : Nat := 4983230072969 + 3 ^ 40 * 2842680 * 2
def baseEnd_2842680 : Nat := 162184576324782581680751

theorem tailTrace_2842680 : CollatzResearch.WordTrace tailWord_2842680 prefixEnd_2842680 162184576324782581680751 := by
  unfold tailWord_2842680
  simp only [CollatzResearch.WordTrace]
  refine ⟨51840528670731662968594747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69120704894308883958126329 51840528670731662968594747)
  ·
    refine ⟨77760793006097494452892121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51840528670731662968594747 77760793006097494452892121)
    ·
      refine ⟨58320594754573120839669091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77760793006097494452892121 58320594754573120839669091)
      ·
        refine ⟨87480892131859681259503637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58320594754573120839669091 87480892131859681259503637)
        ·
          refine ⟨4100666818680922559039233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87480892131859681259503637 4100666818680922559039233)
          ·
            refine ⟨3075500114010691919279425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4100666818680922559039233 3075500114010691919279425)
            ·
              refine ⟨2306625085508018939459569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3075500114010691919279425 2306625085508018939459569)
              ·
                refine ⟨1729968814131014204594677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2306625085508018939459569 1729968814131014204594677)
                ·
                  refine ⟨162184576324782581680751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1729968814131014204594677 162184576324782581680751)
                  ·
                    rfl

theorem cell23_2842680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 5].length) (baseStart_2842680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842680 prefixEnd_2842680 := by exact prefixLift 2842680
  have htrace : WordTrace (prefixWord ++ tailWord_2842680) baseStart_2842680 baseEnd_2842680 := by
    simpa [prefixWord, tailWord_2842680, baseEnd_2842680] using wordTrace_append hprefix tailTrace_2842680
  have hstable : (prefixWord ++ tailWord_2842680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842680).length < 2 ^ (prefixWord ++ tailWord_2842680).sum := by decide
  have hdescent : baseEnd_2842680 < baseStart_2842680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842699 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 3]
def baseStart_2842699 : Nat := 118140960795 + 2842699 * 2 ^ 59
def prefixEnd_2842699 : Nat := 4983230072969 + 3 ^ 40 * 2842699 * 2
def baseEnd_2842699 : Nat := 1459670943055478660789171

theorem tailTrace_2842699 : CollatzResearch.WordTrace tailWord_2842699 prefixEnd_2842699 1459670943055478660789171 := by
  unfold tailWord_2842699
  simp only [CollatzResearch.WordTrace]
  refine ⟨103681750328394492182131151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69121166885596328121420767 103681750328394492182131151)
  ·
    refine ⟨155522625492591738273196727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103681750328394492182131151 155522625492591738273196727)
    ·
      refine ⟨233283938238887607409795091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155522625492591738273196727 233283938238887607409795091)
      ·
        refine ⟨349925907358331411114692637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233283938238887607409795091 349925907358331411114692637)
        ·
          refine ⟨131222215259374279168009739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349925907358331411114692637 131222215259374279168009739)
          ·
            refine ⟨196833322889061418752014609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131222215259374279168009739 196833322889061418752014609)
            ·
              refine ⟨147624992166796064064010957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196833322889061418752014609 147624992166796064064010957)
              ·
                refine ⟨55359372062548524024004109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147624992166796064064010957 55359372062548524024004109)
                ·
                  refine ⟨20759764523455696509001541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55359372062548524024004109 20759764523455696509001541)
                  ·
                    refine ⟨3892455848147943095437789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20759764523455696509001541 3892455848147943095437789)
                    ·
                      refine ⟨1459670943055478660789171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3892455848147943095437789 1459670943055478660789171)
                      ·
                        rfl

theorem cell23_2842699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 3].length) (baseStart_2842699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842699 prefixEnd_2842699 := by exact prefixLift 2842699
  have htrace : WordTrace (prefixWord ++ tailWord_2842699) baseStart_2842699 baseEnd_2842699 := by
    simpa [prefixWord, tailWord_2842699, baseEnd_2842699] using wordTrace_append hprefix tailTrace_2842699
  have hstable : (prefixWord ++ tailWord_2842699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842699).length < 2 ^ (prefixWord ++ tailWord_2842699).sum := by decide
  have hdescent : baseEnd_2842699 < baseStart_2842699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842710 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2842710 : Nat := 118140960795 + 2842710 * 2 ^ 59
def prefixEnd_2842710 : Nat := 4983230072969 + 3 ^ 40 * 2842710 * 2
def baseEnd_2842710 : Nat := 486558863780892705917207

theorem tailTrace_2842710 : CollatzResearch.WordTrace tailWord_2842710 prefixEnd_2842710 486558863780892705917207 := by
  unfold tailWord_2842710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6480134470709665066298849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69121434354236427373854389 6480134470709665066298849)
  ·
    refine ⟨4860100853032248799724137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6480134470709665066298849 4860100853032248799724137)
    ·
      refine ⟨3645075639774186599793103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4860100853032248799724137 3645075639774186599793103)
      ·
        refine ⟨5467613459661279899689655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3645075639774186599793103 5467613459661279899689655)
        ·
          refine ⟨8201420189491919849534483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5467613459661279899689655 8201420189491919849534483)
          ·
            refine ⟨12302130284237879774301725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8201420189491919849534483 12302130284237879774301725)
            ·
              refine ⟨4613298856589204915363147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12302130284237879774301725 4613298856589204915363147)
              ·
                refine ⟨6919948284883807373044721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4613298856589204915363147 6919948284883807373044721)
                ·
                  refine ⟨5189961213662855529783541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6919948284883807373044721 5189961213662855529783541)
                  ·
                    refine ⟨486558863780892705917207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5189961213662855529783541 486558863780892705917207)
                    ·
                      rfl

theorem cell23_2842710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2842710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842710 prefixEnd_2842710 := by exact prefixLift 2842710
  have htrace : WordTrace (prefixWord ++ tailWord_2842710) baseStart_2842710 baseEnd_2842710 := by
    simpa [prefixWord, tailWord_2842710, baseEnd_2842710] using wordTrace_append hprefix tailTrace_2842710
  have hstable : (prefixWord ++ tailWord_2842710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842710).length < 2 ^ (prefixWord ++ tailWord_2842710).sum := by decide
  have hdescent : baseEnd_2842710 < baseStart_2842710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842723 : List Nat := [1, 1, 1, 5, 1, 1, 3, 5, 1, 4]
def baseStart_2842723 : Nat := 118140960795 + 2842723 * 2 ^ 59
def prefixEnd_2842723 : Nat := 4983230072969 + 3 ^ 40 * 2842723 * 2
def baseEnd_2842723 : Nat := 486561088863728855629687

theorem tailTrace_2842723 : CollatzResearch.WordTrace tailWord_2842723 prefixEnd_2842723 486561088863728855629687 := by
  unfold tailWord_2842723
  simp only [CollatzResearch.WordTrace]
  refine ⟨103682625680307544281004823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69121750453538362854003215 103682625680307544281004823)
  ·
    refine ⟨155523938520461316421507235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103682625680307544281004823 155523938520461316421507235)
    ·
      refine ⟨233285907780691974632260853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155523938520461316421507235 233285907780691974632260853)
      ·
        refine ⟨21870553854439872621774455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 233285907780691974632260853 21870553854439872621774455)
        ·
          refine ⟨32805830781659808932661683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21870553854439872621774455 32805830781659808932661683)
          ·
            refine ⟨49208746172489713398992525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32805830781659808932661683 49208746172489713398992525)
            ·
              refine ⟨18453279814683642524622197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49208746172489713398992525 18453279814683642524622197)
              ·
                refine ⟨1729994982626591486683331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18453279814683642524622197 1729994982626591486683331)
                ·
                  refine ⟨2594992473939887230024997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1729994982626591486683331 2594992473939887230024997)
                  ·
                    refine ⟨486561088863728855629687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2594992473939887230024997 486561088863728855629687)
                    ·
                      rfl

theorem cell23_2842723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 1, 4].length) (baseStart_2842723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842723 prefixEnd_2842723 := by exact prefixLift 2842723
  have htrace : WordTrace (prefixWord ++ tailWord_2842723) baseStart_2842723 baseEnd_2842723 := by
    simpa [prefixWord, tailWord_2842723, baseEnd_2842723] using wordTrace_append hprefix tailTrace_2842723
  have hstable : (prefixWord ++ tailWord_2842723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842723).length < 2 ^ (prefixWord ++ tailWord_2842723).sum := by decide
  have hdescent : baseEnd_2842723 < baseStart_2842723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842736 : List Nat := [2, 1, 1, 1, 5, 2, 3, 2, 6]
def baseStart_2842736 : Nat := 118140960795 + 2842736 * 2 ^ 59
def prefixEnd_2842736 : Nat := 4983230072969 + 3 ^ 40 * 2842736 * 2
def baseEnd_2842736 : Nat := 162187771315521668447389

theorem tailTrace_2842736 : CollatzResearch.WordTrace tailWord_2842736 prefixEnd_2842736 162187771315521668447389 := by
  unfold tailWord_2842736
  simp only [CollatzResearch.WordTrace]
  refine ⟨51841549914630223750614031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69122066552840298334152041 51841549914630223750614031)
  ·
    refine ⟨77762324871945335625921047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51841549914630223750614031 77762324871945335625921047)
    ·
      refine ⟨116643487307918003438881571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77762324871945335625921047 116643487307918003438881571)
      ·
        refine ⟨174965230961877005158322357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116643487307918003438881571 174965230961877005158322357)
        ·
          refine ⟨16402990402675969233592721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174965230961877005158322357 16402990402675969233592721)
          ·
            refine ⟨12302242802006976925194541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16402990402675969233592721 12302242802006976925194541)
            ·
              refine ⟨4613341050752616346947953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12302242802006976925194541 4613341050752616346947953)
              ·
                refine ⟨3460005788064462260210965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4613341050752616346947953 3460005788064462260210965)
                ·
                  refine ⟨162187771315521668447389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3460005788064462260210965 162187771315521668447389)
                  ·
                    rfl

theorem cell23_2842736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 6].length) (baseStart_2842736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842736 prefixEnd_2842736 := by exact prefixLift 2842736
  have htrace : WordTrace (prefixWord ++ tailWord_2842736) baseStart_2842736 baseEnd_2842736 := by
    simpa [prefixWord, tailWord_2842736, baseEnd_2842736] using wordTrace_append hprefix tailTrace_2842736
  have hstable : (prefixWord ++ tailWord_2842736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842736).length < 2 ^ (prefixWord ++ tailWord_2842736).sum := by decide
  have hdescent : baseEnd_2842736 < baseStart_2842736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842759 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_2842759 : Nat := 118140960795 + 2842759 * 2 ^ 59
def prefixEnd_2842759 : Nat := 4983230072969 + 3 ^ 40 * 2842759 * 2
def baseEnd_2842759 : Nat := 1459701751894748426038895

theorem tailTrace_2842759 : CollatzResearch.WordTrace tailWord_2842759 prefixEnd_2842759 1459701751894748426038895 := by
  unfold tailWord_2842759
  simp only [CollatzResearch.WordTrace]
  refine ⟨103683938708177122429315331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69122625805451414952876887 103683938708177122429315331)
  ·
    refine ⟨155525908062265683643972997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103683938708177122429315331 155525908062265683643972997)
    ·
      refine ⟨29161107761674815683244937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155525908062265683643972997 29161107761674815683244937)
      ·
        refine ⟨21870830821256111762433703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29161107761674815683244937 21870830821256111762433703)
        ·
          refine ⟨32806246231884167643650555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21870830821256111762433703 32806246231884167643650555)
          ·
            refine ⟨49209369347826251465475833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32806246231884167643650555 49209369347826251465475833)
            ·
              refine ⟨36907027010869688599106875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49209369347826251465475833 36907027010869688599106875)
              ·
                refine ⟨55360540516304532898660313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36907027010869688599106875 55360540516304532898660313)
                ·
                  refine ⟨41520405387228399673995235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55360540516304532898660313 41520405387228399673995235)
                  ·
                    refine ⟨62280608080842599510992853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41520405387228399673995235 62280608080842599510992853)
                    ·
                      refine ⟨1459701751894748426038895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62280608080842599510992853 1459701751894748426038895)
                      ·
                        rfl

theorem cell23_2842759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_2842759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842759 prefixEnd_2842759 := by exact prefixLift 2842759
  have htrace : WordTrace (prefixWord ++ tailWord_2842759) baseStart_2842759 baseEnd_2842759 := by
    simpa [prefixWord, tailWord_2842759, baseEnd_2842759] using wordTrace_append hprefix tailTrace_2842759
  have hstable : (prefixWord ++ tailWord_2842759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842759).length < 2 ^ (prefixWord ++ tailWord_2842759).sum := by decide
  have hdescent : baseEnd_2842759 < baseStart_2842759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842769 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_2842769 : Nat := 118140960795 + 2842769 * 2 ^ 59
def prefixEnd_2842769 : Nat := 4983230072969 + 3 ^ 40 * 2842769 * 2
def baseEnd_2842769 : Nat := 1459706886701293386913849

theorem tailTrace_2842769 : CollatzResearch.WordTrace tailWord_2842769 prefixEnd_2842769 1459706886701293386913849 := by
  unfold tailWord_2842769
  simp only [CollatzResearch.WordTrace]
  refine ⟨103684303438140894137179361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69122868958760596091452907 103684303438140894137179361)
  ·
    refine ⟨77763227578605670602884521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103684303438140894137179361 77763227578605670602884521)
    ·
      refine ⟨58322420683954252952163391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77763227578605670602884521 58322420683954252952163391)
      ·
        refine ⟨87483631025931379428245087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58322420683954252952163391 87483631025931379428245087)
        ·
          refine ⟨131225446538897069142367631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87483631025931379428245087 131225446538897069142367631)
          ·
            refine ⟨196838169808345603713551447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131225446538897069142367631 196838169808345603713551447)
            ·
              refine ⟨295257254712518405570327171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196838169808345603713551447 295257254712518405570327171)
              ·
                refine ⟨442885882068777608355490757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295257254712518405570327171 442885882068777608355490757)
                ·
                  refine ⟨83041102887895801566654517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 442885882068777608355490757 83041102887895801566654517)
                  ·
                    refine ⟨7785103395740231396873861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83041102887895801566654517 7785103395740231396873861)
                    ·
                      refine ⟨1459706886701293386913849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7785103395740231396873861 1459706886701293386913849)
                      ·
                        rfl

theorem cell23_2842769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_2842769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842769 prefixEnd_2842769 := by exact prefixLift 2842769
  have htrace : WordTrace (prefixWord ++ tailWord_2842769) baseStart_2842769 baseEnd_2842769 := by
    simpa [prefixWord, tailWord_2842769, baseEnd_2842769] using wordTrace_append hprefix tailTrace_2842769
  have hstable : (prefixWord ++ tailWord_2842769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842769).length < 2 ^ (prefixWord ++ tailWord_2842769).sum := by decide
  have hdescent : baseEnd_2842769 < baseStart_2842769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842773 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 2, 3, 2]
def baseStart_2842773 : Nat := 118140960795 + 2842773 * 2 ^ 59
def prefixEnd_2842773 : Nat := 4983230072969 + 3 ^ 40 * 2842773 * 2
def baseEnd_2842773 : Nat := 1459708940623911371263831

theorem tailTrace_2842773 : CollatzResearch.WordTrace tailWord_2842773 prefixEnd_2842773 1459708940623911371263831 := by
  unfold tailWord_2842773
  simp only [CollatzResearch.WordTrace]
  refine ⟨103684449330126402820324973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69122966220084268546883315 103684449330126402820324973)
  ·
    refine ⟨38881668498797401057621865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103684449330126402820324973 38881668498797401057621865)
    ·
      refine ⟨29161251374098050793216399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38881668498797401057621865 29161251374098050793216399)
      ·
        refine ⟨43741877061147076189824599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29161251374098050793216399 43741877061147076189824599)
        ·
          refine ⟨65612815591720614284736899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43741877061147076189824599 65612815591720614284736899)
          ·
            refine ⟨98419223387580921427105349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65612815591720614284736899 98419223387580921427105349)
            ·
              refine ⟨18453604385171422767582253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98419223387580921427105349 18453604385171422767582253)
              ·
                refine ⟨6920101644439283537843345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18453604385171422767582253 6920101644439283537843345)
                ·
                  refine ⟨5190076233329462653382509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6920101644439283537843345 5190076233329462653382509)
                  ·
                    refine ⟨1946278587498548495018441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5190076233329462653382509 1946278587498548495018441)
                    ·
                      refine ⟨1459708940623911371263831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1946278587498548495018441 1459708940623911371263831)
                      ·
                        rfl

theorem cell23_2842773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_2842773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842773 prefixEnd_2842773 := by exact prefixLift 2842773
  have htrace : WordTrace (prefixWord ++ tailWord_2842773) baseStart_2842773 baseEnd_2842773 := by
    simpa [prefixWord, tailWord_2842773, baseEnd_2842773] using wordTrace_append hprefix tailTrace_2842773
  have hstable : (prefixWord ++ tailWord_2842773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842773).length < 2 ^ (prefixWord ++ tailWord_2842773).sum := by decide
  have hdescent : baseEnd_2842773 < baseStart_2842773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842783 : List Nat := [1, 1, 2, 6, 1, 1, 2, 3, 1, 5]
def baseStart_2842783 : Nat := 118140960795 + 2842783 * 2 ^ 59
def prefixEnd_2842783 : Nat := 4983230072969 + 3 ^ 40 * 2842783 * 2
def baseEnd_2842783 : Nat := 486571358476818777379595

theorem tailTrace_2842783 : CollatzResearch.WordTrace tailWord_2842783 prefixEnd_2842783 486571358476818777379595 := by
  unfold tailWord_2842783
  simp only [CollatzResearch.WordTrace]
  refine ⟨103684814060090174528189003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69123209373393449685459335 103684814060090174528189003)
  ·
    refine ⟨155527221090135261792283505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103684814060090174528189003 155527221090135261792283505)
    ·
      refine ⟨116645415817601446344212629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155527221090135261792283505 116645415817601446344212629)
      ·
        refine ⟨5467753866450067797384967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 116645415817601446344212629 5467753866450067797384967)
        ·
          refine ⟨8201630799675101696077451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5467753866450067797384967 8201630799675101696077451)
          ·
            refine ⟨12302446199512652544116177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8201630799675101696077451 12302446199512652544116177)
            ·
              refine ⟨9226834649634489408087133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12302446199512652544116177 9226834649634489408087133)
              ·
                refine ⟨3460062993612933528032675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9226834649634489408087133 3460062993612933528032675)
                ·
                  refine ⟨5190094490419400292049013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460062993612933528032675 5190094490419400292049013)
                  ·
                    refine ⟨486571358476818777379595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5190094490419400292049013 486571358476818777379595)
                    ·
                      rfl

theorem cell23_2842783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 5].length) (baseStart_2842783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842783 prefixEnd_2842783 := by exact prefixLift 2842783
  have htrace : WordTrace (prefixWord ++ tailWord_2842783) baseStart_2842783 baseEnd_2842783 := by
    simpa [prefixWord, tailWord_2842783, baseEnd_2842783] using wordTrace_append hprefix tailTrace_2842783
  have hstable : (prefixWord ++ tailWord_2842783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842783).length < 2 ^ (prefixWord ++ tailWord_2842783).sum := by decide
  have hdescent : baseEnd_2842783 < baseStart_2842783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842797 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_2842797 : Nat := 118140960795 + 2842797 * 2 ^ 59
def prefixEnd_2842797 : Nat := 4983230072969 + 3 ^ 40 * 2842797 * 2
def baseEnd_2842797 : Nat := 1459721264159619277363721

theorem tailTrace_2842797 : CollatzResearch.WordTrace tailWord_2842797 prefixEnd_2842797 1459721264159619277363721 := by
  unfold tailWord_2842797
  simp only [CollatzResearch.WordTrace]
  refine ⟨103685324682039454919198645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69123549788026303279465763 103685324682039454919198645)
  ·
    refine ⟨9720499188941198898674873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103685324682039454919198645 9720499188941198898674873)
    ·
      refine ⟨7290374391705899174006155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9720499188941198898674873 7290374391705899174006155)
      ·
        refine ⟨10935561587558848761009233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7290374391705899174006155 10935561587558848761009233)
        ·
          refine ⟨8201671190669136570756925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10935561587558848761009233 8201671190669136570756925)
          ·
            refine ⟨3075626696500926214033847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8201671190669136570756925 3075626696500926214033847)
            ·
              refine ⟨4613440044751389321050771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3075626696500926214033847 4613440044751389321050771)
              ·
                refine ⟨6920160067127083981576157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4613440044751389321050771 6920160067127083981576157)
                ·
                  refine ⟨2595060025172656493091059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6920160067127083981576157 2595060025172656493091059)
                  ·
                    refine ⟨3892590037758984739636589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2595060025172656493091059 3892590037758984739636589)
                    ·
                      refine ⟨1459721264159619277363721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3892590037758984739636589 1459721264159619277363721)
                      ·
                        rfl

theorem cell23_2842797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_2842797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842797 prefixEnd_2842797 := by exact prefixLift 2842797
  have htrace : WordTrace (prefixWord ++ tailWord_2842797) baseStart_2842797 baseEnd_2842797 := by
    simpa [prefixWord, tailWord_2842797, baseEnd_2842797] using wordTrace_append hprefix tailTrace_2842797
  have hstable : (prefixWord ++ tailWord_2842797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842797).length < 2 ^ (prefixWord ++ tailWord_2842797).sum := by decide
  have hdescent : baseEnd_2842797 < baseStart_2842797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842816 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 6]
def baseStart_2842816 : Nat := 118140960795 + 2842816 * 2 ^ 59
def prefixEnd_2842816 : Nat := 4983230072969 + 3 ^ 40 * 2842816 * 2
def baseEnd_2842816 : Nat := 1459731020292054703026133

theorem tailTrace_2842816 : CollatzResearch.WordTrace tailWord_2842816 prefixEnd_2842816 1459731020292054703026133 := by
  unfold tailWord_2842816
  simp only [CollatzResearch.WordTrace]
  refine ⟨51843008834485310582070151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69124011779313747442760201 51843008834485310582070151)
  ·
    refine ⟨77764513251727965873105227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51843008834485310582070151 77764513251727965873105227)
    ·
      refine ⟨116646769877591948809657841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77764513251727965873105227 116646769877591948809657841)
      ·
        refine ⟨87485077408193961607243381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116646769877591948809657841 87485077408193961607243381)
        ·
          refine ⟨8201726007018183900679067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87485077408193961607243381 8201726007018183900679067)
          ·
            refine ⟨12302589010527275851018601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8201726007018183900679067 12302589010527275851018601)
            ·
              refine ⟨9226941757895456888263951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12302589010527275851018601 9226941757895456888263951)
              ·
                refine ⟨13840412636843185332395927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9226941757895456888263951 13840412636843185332395927)
                ·
                  refine ⟨20760618955264777998593891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13840412636843185332395927 20760618955264777998593891)
                  ·
                    refine ⟨31140928432897166997890837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20760618955264777998593891 31140928432897166997890837)
                    ·
                      refine ⟨1459731020292054703026133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31140928432897166997890837 1459731020292054703026133)
                      ·
                        rfl

theorem cell23_2842816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_2842816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842816 prefixEnd_2842816 := by exact prefixLift 2842816
  have htrace : WordTrace (prefixWord ++ tailWord_2842816) baseStart_2842816 baseEnd_2842816 := by
    simpa [prefixWord, tailWord_2842816, baseEnd_2842816] using wordTrace_append hprefix tailTrace_2842816
  have hstable : (prefixWord ++ tailWord_2842816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842816).length < 2 ^ (prefixWord ++ tailWord_2842816).sum := by decide
  have hdescent : baseEnd_2842816 < baseStart_2842816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842817 : List Nat := [1, 2, 6, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2842817 : Nat := 118140960795 + 2842817 * 2 ^ 59
def prefixEnd_2842817 : Nat := 4983230072969 + 3 ^ 40 * 2842817 * 2
def baseEnd_2842817 : Nat := 486577177924236399704543

theorem tailTrace_2842817 : CollatzResearch.WordTrace tailWord_2842817 prefixEnd_2842817 486577177924236399704543 := by
  unfold tailWord_2842817
  simp only [CollatzResearch.WordTrace]
  refine ⟨103686054141966998334926705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69124036094644665556617803 103686054141966998334926705)
  ·
    refine ⟨77764540606475248751195029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103686054141966998334926705 77764540606475248751195029)
    ·
      refine ⟨3645212840928527285212267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77764540606475248751195029 3645212840928527285212267)
      ·
        refine ⟨5467819261392790927818401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3645212840928527285212267 5467819261392790927818401)
        ·
          refine ⟨4100864446044593195863801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5467819261392790927818401 4100864446044593195863801)
          ·
            refine ⟨3075648334533444896897851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4100864446044593195863801 3075648334533444896897851)
            ·
              refine ⟨4613472501800167345346777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3075648334533444896897851 4613472501800167345346777)
              ·
                refine ⟨3460104376350125509010083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4613472501800167345346777 3460104376350125509010083)
                ·
                  refine ⟨5190156564525188263515125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460104376350125509010083 5190156564525188263515125)
                  ·
                    refine ⟨486577177924236399704543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5190156564525188263515125 486577177924236399704543)
                    ·
                      rfl

theorem cell23_2842817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2842817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842817 prefixEnd_2842817 := by exact prefixLift 2842817
  have htrace : WordTrace (prefixWord ++ tailWord_2842817) baseStart_2842817 baseEnd_2842817 := by
    simpa [prefixWord, tailWord_2842817, baseEnd_2842817] using wordTrace_append hprefix tailTrace_2842817
  have hstable : (prefixWord ++ tailWord_2842817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842817).length < 2 ^ (prefixWord ++ tailWord_2842817).sum := by decide
  have hdescent : baseEnd_2842817 < baseStart_2842817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842820 : List Nat := [2, 3, 3, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_2842820 : Nat := 118140960795 + 2842820 * 2 ^ 59
def prefixEnd_2842820 : Nat := 4983230072969 + 3 ^ 40 * 2842820 * 2
def baseEnd_2842820 : Nat := 1459733074214672687376115

theorem tailTrace_2842820 : CollatzResearch.WordTrace tailWord_2842820 prefixEnd_2842820 1459733074214672687376115 := by
  unfold tailWord_2842820
  simp only [CollatzResearch.WordTrace]
  refine ⟨51843081780478064923642957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69124109040637419898190609 51843081780478064923642957)
  ·
    refine ⟨19441155667679274346366109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51843081780478064923642957 19441155667679274346366109)
    ·
      refine ⟨7290433375379727879887291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19441155667679274346366109 7290433375379727879887291)
      ·
        refine ⟨10935650063069591819830937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7290433375379727879887291 10935650063069591819830937)
        ·
          refine ⟨8201737547302193864873203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10935650063069591819830937 8201737547302193864873203)
          ·
            refine ⟨12302606320953290797309805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8201737547302193864873203 12302606320953290797309805)
            ·
              refine ⟨4613477370357484048991177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12302606320953290797309805 4613477370357484048991177)
              ·
                refine ⟨3460108027768113036743383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4613477370357484048991177 3460108027768113036743383)
                ·
                  refine ⟨5190162041652169555115075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460108027768113036743383 5190162041652169555115075)
                  ·
                    refine ⟨7785243062478254332672613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5190162041652169555115075 7785243062478254332672613)
                    ·
                      refine ⟨1459733074214672687376115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7785243062478254332672613 1459733074214672687376115)
                      ·
                        rfl

theorem cell23_2842820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_2842820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842820 prefixEnd_2842820 := by exact prefixLift 2842820
  have htrace : WordTrace (prefixWord ++ tailWord_2842820) baseStart_2842820 baseEnd_2842820 := by
    simpa [prefixWord, tailWord_2842820, baseEnd_2842820] using wordTrace_append hprefix tailTrace_2842820
  have hstable : (prefixWord ++ tailWord_2842820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842820).length < 2 ^ (prefixWord ++ tailWord_2842820).sum := by decide
  have hdescent : baseEnd_2842820 < baseStart_2842820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842837 : List Nat := [1, 3, 2, 4, 2, 1, 3, 1, 1, 1, 4]
def baseStart_2842837 : Nat := 118140960795 + 2842837 * 2 ^ 59
def prefixEnd_2842837 : Nat := 4983230072969 + 3 ^ 40 * 2842837 * 2
def baseEnd_2842837 : Nat := 1459741803385799120863537

theorem tailTrace_2842837 : CollatzResearch.WordTrace tailWord_2842837 prefixEnd_2842837 1459741803385799120863537 := by
  unfold tailWord_2842837
  simp only [CollatzResearch.WordTrace]
  refine ⟨103686783601894541750654765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69124522401263027833769843 103686783601894541750654765)
  ·
    refine ⟨38882543850710453156495537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103686783601894541750654765 38882543850710453156495537)
    ·
      refine ⟨29161907888032839867371653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38882543850710453156495537 29161907888032839867371653)
      ·
        refine ⟨5467857729006157475132185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29161907888032839867371653 5467857729006157475132185)
        ·
          refine ⟨4100893296754618106349139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5467857729006157475132185 4100893296754618106349139)
          ·
            refine ⟨6151339945131927159523709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4100893296754618106349139 6151339945131927159523709)
            ·
              refine ⟨2306752479424472684821391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6151339945131927159523709 2306752479424472684821391)
              ·
                refine ⟨3460128719136709027232087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2306752479424472684821391 3460128719136709027232087)
                ·
                  refine ⟨5190193078705063540848131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460128719136709027232087 5190193078705063540848131)
                  ·
                    refine ⟨7785289618057595311272197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5190193078705063540848131 7785289618057595311272197)
                    ·
                      refine ⟨1459741803385799120863537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7785289618057595311272197 1459741803385799120863537)
                      ·
                        rfl

theorem cell23_2842837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_2842837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842837 prefixEnd_2842837 := by exact prefixLift 2842837
  have htrace : WordTrace (prefixWord ++ tailWord_2842837) baseStart_2842837 baseEnd_2842837 := by
    simpa [prefixWord, tailWord_2842837, baseEnd_2842837] using wordTrace_append hprefix tailTrace_2842837
  have hstable : (prefixWord ++ tailWord_2842837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842837).length < 2 ^ (prefixWord ++ tailWord_2842837).sum := by decide
  have hdescent : baseEnd_2842837 < baseStart_2842837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842856 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 2, 7]
def baseStart_2842856 : Nat := 118140960795 + 2842856 * 2 ^ 59
def prefixEnd_2842856 : Nat := 4983230072969 + 3 ^ 40 * 2842856 * 2
def baseEnd_2842856 : Nat := 486583853172744848841983

theorem tailTrace_2842856 : CollatzResearch.WordTrace tailWord_2842856 prefixEnd_2842856 486583853172744848841983 := by
  unfold tailWord_2842856
  simp only [CollatzResearch.WordTrace]
  refine ⟨51843738294412853997798211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69124984392550471997064281 51843738294412853997798211)
  ·
    refine ⟨77765607441619280996697317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51843738294412853997798211 77765607441619280996697317)
    ·
      refine ⟨14581051395303615186880747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77765607441619280996697317 14581051395303615186880747)
      ·
        refine ⟨21871577092955422780321121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14581051395303615186880747 21871577092955422780321121)
        ·
          refine ⟨16403682819716567085240841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21871577092955422780321121 16403682819716567085240841)
          ·
            refine ⟨12302762114787425313930631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16403682819716567085240841 12302762114787425313930631)
            ·
              refine ⟨18454143172181137970895947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12302762114787425313930631 18454143172181137970895947)
              ·
                refine ⟨27681214758271706956343921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18454143172181137970895947 27681214758271706956343921)
                ·
                  refine ⟨20760911068703780217257941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27681214758271706956343921 20760911068703780217257941)
                  ·
                    refine ⟨486583853172744848841983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20760911068703780217257941 486583853172744848841983)
                    ·
                      rfl

theorem cell23_2842856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_2842856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842856 prefixEnd_2842856 := by exact prefixLift 2842856
  have htrace : WordTrace (prefixWord ++ tailWord_2842856) baseStart_2842856 baseEnd_2842856 := by
    simpa [prefixWord, tailWord_2842856, baseEnd_2842856] using wordTrace_append hprefix tailTrace_2842856
  have hstable : (prefixWord ++ tailWord_2842856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842856).length < 2 ^ (prefixWord ++ tailWord_2842856).sum := by decide
  have hdescent : baseEnd_2842856 < baseStart_2842856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842897 : List Nat := [1, 2, 2, 1, 1, 5, 4, 1, 1, 3, 2]
def baseStart_2842897 : Nat := 118140960795 + 2842897 * 2 ^ 59
def prefixEnd_2842897 : Nat := 4983230072969 + 3 ^ 40 * 2842897 * 2
def baseEnd_2842897 : Nat := 1459772612225068886113261

theorem tailTrace_2842897 : CollatzResearch.WordTrace tailWord_2842897 prefixEnd_2842897 1459772612225068886113261 := by
  unfold tailWord_2842897
  simp only [CollatzResearch.WordTrace]
  refine ⟨103688971981677171997838945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69125981321118114665225963 103688971981677171997838945)
  ·
    refine ⟨77766728986257878998379209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103688971981677171997838945 77766728986257878998379209)
    ·
      refine ⟨58325046739693409248784407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77766728986257878998379209 58325046739693409248784407)
      ·
        refine ⟨87487570109540113873176611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58325046739693409248784407 87487570109540113873176611)
        ·
          refine ⟨131231355164310170809764917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87487570109540113873176611 131231355164310170809764917)
          ·
            refine ⟨12302939546654078513415461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131231355164310170809764917 12302939546654078513415461)
            ·
              refine ⟨2306801164997639721265399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12302939546654078513415461 2306801164997639721265399)
              ·
                refine ⟨3460201747496459581898099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2306801164997639721265399 3460201747496459581898099)
                ·
                  refine ⟨5190302621244689372847149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460201747496459581898099 5190302621244689372847149)
                  ·
                    refine ⟨1946363482966758514817681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5190302621244689372847149 1946363482966758514817681)
                    ·
                      refine ⟨1459772612225068886113261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1946363482966758514817681 1459772612225068886113261)
                      ·
                        rfl

theorem cell23_2842897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 1, 3, 2].length) (baseStart_2842897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842897 prefixEnd_2842897 := by exact prefixLift 2842897
  have htrace : WordTrace (prefixWord ++ tailWord_2842897) baseStart_2842897 baseEnd_2842897 := by
    simpa [prefixWord, tailWord_2842897, baseEnd_2842897] using wordTrace_append hprefix tailTrace_2842897
  have hstable : (prefixWord ++ tailWord_2842897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842897).length < 2 ^ (prefixWord ++ tailWord_2842897).sum := by decide
  have hdescent : baseEnd_2842897 < baseStart_2842897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842953 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 1, 7, 2]
def baseStart_2842953 : Nat := 118140960795 + 2842953 * 2 ^ 59
def prefixEnd_2842953 : Nat := 4983230072969 + 3 ^ 40 * 2842953 * 2
def baseEnd_2842953 : Nat := 1459801367141720667013003

theorem tailTrace_2842953 : CollatzResearch.WordTrace tailWord_2842953 prefixEnd_2842953 1459801367141720667013003 := by
  unfold tailWord_2842953
  simp only [CollatzResearch.WordTrace]
  refine ⟨103691014469474293561877513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69127342979649529041251675 103691014469474293561877513)
  ·
    refine ⟨77768260852105720171408135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103691014469474293561877513 77768260852105720171408135)
    ·
      refine ⟨116652391278158580257112203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77768260852105720171408135 116652391278158580257112203)
      ·
        refine ⟨174978586917237870385668305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116652391278158580257112203 174978586917237870385668305)
        ·
          refine ⟨131233940187928402789251229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174978586917237870385668305 131233940187928402789251229)
          ·
            refine ⟨49212727570473151045969211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131233940187928402789251229 49212727570473151045969211)
            ·
              refine ⟨73819091355709726568953817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49212727570473151045969211 73819091355709726568953817)
              ·
                refine ⟨55364318516782294926715363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73819091355709726568953817 55364318516782294926715363)
                ·
                  refine ⟨83046477775173442390073045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55364318516782294926715363 83046477775173442390073045)
                  ·
                    refine ⟨1946401822855627556017337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 83046477775173442390073045 1946401822855627556017337)
                    ·
                      refine ⟨1459801367141720667013003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1946401822855627556017337 1459801367141720667013003)
                      ·
                        rfl

theorem cell23_2842953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 7, 2].length) (baseStart_2842953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842953 prefixEnd_2842953 := by exact prefixLift 2842953
  have htrace : WordTrace (prefixWord ++ tailWord_2842953) baseStart_2842953 baseEnd_2842953 := by
    simpa [prefixWord, tailWord_2842953, baseEnd_2842953] using wordTrace_append hprefix tailTrace_2842953
  have hstable : (prefixWord ++ tailWord_2842953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842953).length < 2 ^ (prefixWord ++ tailWord_2842953).sum := by decide
  have hdescent : baseEnd_2842953 < baseStart_2842953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2842993 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 5, 4]
def baseStart_2842993 : Nat := 118140960795 + 2842993 * 2 ^ 59
def prefixEnd_2842993 : Nat := 4983230072969 + 3 ^ 40 * 2842993 * 2
def baseEnd_2842993 : Nat := 486607302122633503504273

theorem tailTrace_2842993 : CollatzResearch.WordTrace tailWord_2842993 prefixEnd_2842993 486607302122633503504273 := by
  unfold tailWord_2842993
  simp only [CollatzResearch.WordTrace]
  refine ⟨103692473389329380393333633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69128315592886253595555755 103692473389329380393333633)
  ·
    refine ⟨77769355041997035295000225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103692473389329380393333633 77769355041997035295000225)
    ·
      refine ⟨58327016281497776471250169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77769355041997035295000225 58327016281497776471250169)
      ·
        refine ⟨43745262211123332353437627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58327016281497776471250169 43745262211123332353437627)
        ·
          refine ⟨65617893316684998530156441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43745262211123332353437627 65617893316684998530156441)
          ·
            refine ⟨49213419987513748897617331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65617893316684998530156441 49213419987513748897617331)
            ·
              refine ⟨73820129981270623346425997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49213419987513748897617331 73820129981270623346425997)
              ·
                refine ⟨27682548742976483754909749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73820129981270623346425997 27682548742976483754909749)
                ·
                  refine ⟨2595238944654045352022789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27682548742976483754909749 2595238944654045352022789)
                  ·
                    refine ⟨486607302122633503504273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2595238944654045352022789 486607302122633503504273)
                    ·
                      rfl

theorem cell23_2842993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_2842993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2842993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2842993 prefixEnd_2842993 := by exact prefixLift 2842993
  have htrace : WordTrace (prefixWord ++ tailWord_2842993) baseStart_2842993 baseEnd_2842993 := by
    simpa [prefixWord, tailWord_2842993, baseEnd_2842993] using wordTrace_append hprefix tailTrace_2842993
  have hstable : (prefixWord ++ tailWord_2842993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2842993).length < 2 ^ (prefixWord ++ tailWord_2842993).sum := by decide
  have hdescent : baseEnd_2842993 < baseStart_2842993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2842993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843020 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 2, 2, 3]
def baseStart_2843020 : Nat := 118140960795 + 2843020 * 2 ^ 59
def prefixEnd_2843020 : Nat := 4983230072969 + 3 ^ 40 * 2843020 * 2
def baseEnd_2843020 : Nat := 1459835770345571904875195

theorem tailTrace_2843020 : CollatzResearch.WordTrace tailWord_2843020 prefixEnd_2843020 1459835770345571904875195 := by
  unfold tailWord_2843020
  simp only [CollatzResearch.WordTrace]
  refine ⟨51846729080115782002283257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69128972106821042669711009 51846729080115782002283257)
  ·
    refine ⟨38885046810086836501712443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51846729080115782002283257 38885046810086836501712443)
    ·
      refine ⟨58327570215130254752568665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38885046810086836501712443 58327570215130254752568665)
      ·
        refine ⟨43745677661347691064426499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58327570215130254752568665 43745677661347691064426499)
        ·
          refine ⟨65618516492021536596639749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43745677661347691064426499 65618516492021536596639749)
          ·
            refine ⟨12303471842254038111869953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65618516492021536596639749 12303471842254038111869953)
            ·
              refine ⟨9227603881690528583902465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12303471842254038111869953 9227603881690528583902465)
              ·
                refine ⟨6920702911267896437926849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9227603881690528583902465 6920702911267896437926849)
                ·
                  refine ⟨5190527183450922328445137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6920702911267896437926849 5190527183450922328445137)
                  ·
                    refine ⟨3892895387588191746333853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5190527183450922328445137 3892895387588191746333853)
                    ·
                      refine ⟨1459835770345571904875195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3892895387588191746333853 1459835770345571904875195)
                      ·
                        rfl

theorem cell23_2843020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_2843020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843020 prefixEnd_2843020 := by exact prefixLift 2843020
  have htrace : WordTrace (prefixWord ++ tailWord_2843020) baseStart_2843020 baseEnd_2843020 := by
    simpa [prefixWord, tailWord_2843020, baseEnd_2843020] using wordTrace_append hprefix tailTrace_2843020
  have hstable : (prefixWord ++ tailWord_2843020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843020).length < 2 ^ (prefixWord ++ tailWord_2843020).sum := by decide
  have hdescent : baseEnd_2843020 < baseStart_2843020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843084 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 3, 1, 3]
def baseStart_2843084 : Nat := 118140960795 + 2843084 * 2 ^ 59
def prefixEnd_2843084 : Nat := 4983230072969 + 3 ^ 40 * 2843084 * 2
def baseEnd_2843084 : Nat := 1459868633107459654474901

theorem tailTrace_2843084 : CollatzResearch.WordTrace tailWord_2843084 prefixEnd_2843084 1459868633107459654474901 := by
  unfold tailWord_2843084
  simp only [CollatzResearch.WordTrace]
  refine ⟨51847896215999851467448153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69130528287999801956597537 51847896215999851467448153)
  ·
    refine ⟨38885922161999888600586115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51847896215999851467448153 38885922161999888600586115)
    ·
      refine ⟨58328883242999832900879173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38885922161999888600586115 58328883242999832900879173)
      ·
        refine ⟨10936665608062468668914845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58328883242999832900879173 10936665608062468668914845)
        ·
          refine ⟨4101249603023425750843067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10936665608062468668914845 4101249603023425750843067)
          ·
            refine ⟨6151874404535138626264601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101249603023425750843067 6151874404535138626264601)
            ·
              refine ⟨4613905803401353969698451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6151874404535138626264601 4613905803401353969698451)
              ·
                refine ⟨6920858705102030954547677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4613905803401353969698451 6920858705102030954547677)
                ·
                  refine ⟨2595322014413261607955379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6920858705102030954547677 2595322014413261607955379)
                  ·
                    refine ⟨3892983021619892411933069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2595322014413261607955379 3892983021619892411933069)
                    ·
                      refine ⟨1459868633107459654474901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3892983021619892411933069 1459868633107459654474901)
                      ·
                        rfl

theorem cell23_2843084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_2843084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843084 prefixEnd_2843084 := by exact prefixLift 2843084
  have htrace : WordTrace (prefixWord ++ tailWord_2843084) baseStart_2843084 baseEnd_2843084 := by
    simpa [prefixWord, tailWord_2843084, baseEnd_2843084] using wordTrace_append hprefix tailTrace_2843084
  have hstable : (prefixWord ++ tailWord_2843084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843084).length < 2 ^ (prefixWord ++ tailWord_2843084).sum := by decide
  have hdescent : baseEnd_2843084 < baseStart_2843084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843117 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_2843117 : Nat := 118140960795 + 2843117 * 2 ^ 59
def prefixEnd_2843117 : Nat := 4983230072969 + 3 ^ 40 * 2843117 * 2
def baseEnd_2843117 : Nat := 486628525989686008454083

theorem tailTrace_2843117 : CollatzResearch.WordTrace tailWord_2843117 prefixEnd_2843117 486628525989686008454083 := by
  unfold tailWord_2843117
  simp only [CollatzResearch.WordTrace]
  refine ⟨103696996040880149570847605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69131330693920099713898403 103696996040880149570847605)
  ·
    refine ⟨9721593378832514022266963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103696996040880149570847605 9721593378832514022266963)
    ·
      refine ⟨14582390068248771033400445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9721593378832514022266963 14582390068248771033400445)
      ·
        refine ⟨5468396275593289137525167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14582390068248771033400445 5468396275593289137525167)
        ·
          refine ⟨8202594413389933706287751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5468396275593289137525167 8202594413389933706287751)
          ·
            refine ⟨12303891620084900559431627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8202594413389933706287751 12303891620084900559431627)
            ·
              refine ⟨18455837430127350839147441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12303891620084900559431627 18455837430127350839147441)
              ·
                refine ⟨13841878072595513129360581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18455837430127350839147441 13841878072595513129360581)
                ·
                  refine ⟨2595352138611658711755109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13841878072595513129360581 2595352138611658711755109)
                  ·
                    refine ⟨486628525989686008454083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2595352138611658711755109 486628525989686008454083)
                    ·
                      rfl

theorem cell23_2843117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_2843117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843117 prefixEnd_2843117 := by exact prefixLift 2843117
  have htrace : WordTrace (prefixWord ++ tailWord_2843117) baseStart_2843117 baseEnd_2843117 := by
    simpa [prefixWord, tailWord_2843117, baseEnd_2843117] using wordTrace_append hprefix tailTrace_2843117
  have hstable : (prefixWord ++ tailWord_2843117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843117).length < 2 ^ (prefixWord ++ tailWord_2843117).sum := by decide
  have hdescent : baseEnd_2843117 < baseStart_2843117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843153 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_2843153 : Nat := 118140960795 + 2843153 * 2 ^ 59
def prefixEnd_2843153 : Nat := 4983230072969 + 3 ^ 40 * 2843153 * 2
def baseEnd_2843153 : Nat := 1459904063272619884512083

theorem tailTrace_2843153 : CollatzResearch.WordTrace tailWord_2843153 prefixEnd_2843153 1459904063272619884512083 := by
  unfold tailWord_2843153
  simp only [CollatzResearch.WordTrace]
  refine ⟨103698309068749727719158113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69132206045833151812772075 103698309068749727719158113)
  ·
    refine ⟨77773731801562295789368585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103698309068749727719158113 77773731801562295789368585)
    ·
      refine ⟨58330298851171721842026439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77773731801562295789368585 58330298851171721842026439)
      ·
        refine ⟨87495448276757582763039659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58330298851171721842026439 87495448276757582763039659)
        ·
          refine ⟨131243172415136374144559489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87495448276757582763039659 131243172415136374144559489)
          ·
            refine ⟨98432379311352280608419617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131243172415136374144559489 98432379311352280608419617)
            ·
              refine ⟨73824284483514210456314713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98432379311352280608419617 73824284483514210456314713)
              ·
                refine ⟨55368213362635657842236035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73824284483514210456314713 55368213362635657842236035)
                ·
                  refine ⟨83052320043953486763354053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55368213362635657842236035 83052320043953486763354053)
                  ·
                    refine ⟨15572310008241278768128885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83052320043953486763354053 15572310008241278768128885)
                    ·
                      refine ⟨1459904063272619884512083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15572310008241278768128885 1459904063272619884512083)
                      ·
                        rfl

theorem cell23_2843153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_2843153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843153 prefixEnd_2843153 := by exact prefixLift 2843153
  have htrace : WordTrace (prefixWord ++ tailWord_2843153) baseStart_2843153 baseEnd_2843153 := by
    simpa [prefixWord, tailWord_2843153, baseEnd_2843153] using wordTrace_append hprefix tailTrace_2843153
  have hstable : (prefixWord ++ tailWord_2843153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843153).length < 2 ^ (prefixWord ++ tailWord_2843153).sum := by decide
  have hdescent : baseEnd_2843153 < baseStart_2843153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843200 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 3]
def baseStart_2843200 : Nat := 118140960795 + 2843200 * 2 ^ 59
def prefixEnd_2843200 : Nat := 4983230072969 + 3 ^ 40 * 2843200 * 2
def baseEnd_2843200 : Nat := 1459928196863381200624367

theorem tailTrace_2843200 : CollatzResearch.WordTrace tailWord_2843200 prefixEnd_2843200 1459928196863381200624367 := by
  unfold tailWord_2843200
  simp only [CollatzResearch.WordTrace]
  refine ⟨51850011649789727373059527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69133348866386303164079369 51850011649789727373059527)
  ·
    refine ⟨77775017474684591059589291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51850011649789727373059527 77775017474684591059589291)
    ·
      refine ⟨116662526212026886589383937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77775017474684591059589291 116662526212026886589383937)
      ·
        refine ⟨87496894659020164942037953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116662526212026886589383937 87496894659020164942037953)
        ·
          refine ⟨65622670994265123706528465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87496894659020164942037953 65622670994265123706528465)
          ·
            refine ⟨49217003245698842779896349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65622670994265123706528465 49217003245698842779896349)
            ·
              refine ⟨18456376217137066042461131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49217003245698842779896349 18456376217137066042461131)
              ·
                refine ⟨27684564325705599063691697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18456376217137066042461131 27684564325705599063691697)
                ·
                  refine ⟨20763423244279199297768773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27684564325705599063691697 20763423244279199297768773)
                  ·
                    refine ⟨3893141858302349868331645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20763423244279199297768773 3893141858302349868331645)
                    ·
                      refine ⟨1459928196863381200624367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3893141858302349868331645 1459928196863381200624367)
                      ·
                        rfl

theorem cell23_2843200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_2843200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843200 prefixEnd_2843200 := by exact prefixLift 2843200
  have htrace : WordTrace (prefixWord ++ tailWord_2843200) baseStart_2843200 baseEnd_2843200 := by
    simpa [prefixWord, tailWord_2843200, baseEnd_2843200] using wordTrace_append hprefix tailTrace_2843200
  have hstable : (prefixWord ++ tailWord_2843200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843200).length < 2 ^ (prefixWord ++ tailWord_2843200).sum := by decide
  have hdescent : baseEnd_2843200 < baseStart_2843200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843203 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 11]
def baseStart_2843203 : Nat := 118140960795 + 2843203 * 2 ^ 59
def prefixEnd_2843203 : Nat := 4983230072969 + 3 ^ 40 * 2843203 * 2
def baseEnd_2843203 : Nat := 162214415256149409876317

theorem tailTrace_2843203 : CollatzResearch.WordTrace tailWord_2843203 prefixEnd_2843203 162214415256149409876317 := by
  unfold tailWord_2843203
  simp only [CollatzResearch.WordTrace]
  refine ⟨103700132718568586258478263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69133421812379057505652175 103700132718568586258478263)
  ·
    refine ⟨155550199077852879387717395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103700132718568586258478263 155550199077852879387717395)
    ·
      refine ⟨233325298616779319081576093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155550199077852879387717395 233325298616779319081576093)
      ·
        refine ⟨87496986981292244655591035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233325298616779319081576093 87496986981292244655591035)
        ·
          refine ⟨131245480471938366983386553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87496986981292244655591035 131245480471938366983386553)
          ·
            refine ⟨98434110353953775237539915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131245480471938366983386553 98434110353953775237539915)
            ·
              refine ⟨147651165530930662856309873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98434110353953775237539915 147651165530930662856309873)
              ·
                refine ⟨110738374148197997142232405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147651165530930662856309873 110738374148197997142232405)
                ·
                  refine ⟨162214415256149409876317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 110738374148197997142232405 162214415256149409876317)
                  ·
                    rfl

theorem cell23_2843203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 11].length) (baseStart_2843203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843203 prefixEnd_2843203 := by exact prefixLift 2843203
  have htrace : WordTrace (prefixWord ++ tailWord_2843203) baseStart_2843203 baseEnd_2843203 := by
    simpa [prefixWord, tailWord_2843203, baseEnd_2843203] using wordTrace_append hprefix tailTrace_2843203
  have hstable : (prefixWord ++ tailWord_2843203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843203).length < 2 ^ (prefixWord ++ tailWord_2843203).sum := by decide
  have hdescent : baseEnd_2843203 < baseStart_2843203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843210 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_2843210 : Nat := 118140960795 + 2843210 * 2 ^ 59
def prefixEnd_2843210 : Nat := 4983230072969 + 3 ^ 40 * 2843210 * 2
def baseEnd_2843210 : Nat := 1459933331669926161499321

theorem tailTrace_2843210 : CollatzResearch.WordTrace tailWord_2843210 prefixEnd_2843210 1459933331669926161499321 := by
  unfold tailWord_2843210
  simp only [CollatzResearch.WordTrace]
  refine ⟨25925097007385806613495771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69133592019695484302655389 25925097007385806613495771)
  ·
    refine ⟨38887645511078709920243657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25925097007385806613495771 38887645511078709920243657)
    ·
      refine ⟨29165734133309032440182743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38887645511078709920243657 29165734133309032440182743)
      ·
        refine ⟨43748601199963548660274115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29165734133309032440182743 43748601199963548660274115)
        ·
          refine ⟨65622901799945322990411173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43748601199963548660274115 65622901799945322990411173)
          ·
            refine ⟨12304294087489748060702095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65622901799945322990411173 12304294087489748060702095)
            ·
              refine ⟨18456441131234622091053143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12304294087489748060702095 18456441131234622091053143)
              ·
                refine ⟨27684661696851933136579715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18456441131234622091053143 27684661696851933136579715)
                ·
                  refine ⟨41526992545277899704869573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27684661696851933136579715 41526992545277899704869573)
                  ·
                    refine ⟨7786311102239606194663045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41526992545277899704869573 7786311102239606194663045)
                    ·
                      refine ⟨1459933331669926161499321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7786311102239606194663045 1459933331669926161499321)
                      ·
                        rfl

theorem cell23_2843210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_2843210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843210 prefixEnd_2843210 := by exact prefixLift 2843210
  have htrace : WordTrace (prefixWord ++ tailWord_2843210) baseStart_2843210 baseEnd_2843210 := by
    simpa [prefixWord, tailWord_2843210, baseEnd_2843210] using wordTrace_append hprefix tailTrace_2843210
  have hstable : (prefixWord ++ tailWord_2843210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843210).length < 2 ^ (prefixWord ++ tailWord_2843210).sum := by decide
  have hdescent : baseEnd_2843210 < baseStart_2843210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843220 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 9]
def baseStart_2843220 : Nat := 118140960795 + 2843220 * 2 ^ 59
def prefixEnd_2843220 : Nat := 4983230072969 + 3 ^ 40 * 2843220 * 2
def baseEnd_2843220 : Nat := 162215385164052346930475

theorem tailTrace_2843220 : CollatzResearch.WordTrace tailWord_2843220 prefixEnd_2843220 162215385164052346930475 := by
  unfold tailWord_2843220
  simp only [CollatzResearch.WordTrace]
  refine ⟨51850376379753499080923557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69133835173004665441231409 51850376379753499080923557)
  ·
    refine ⟨9721945571203781077673167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51850376379753499080923557 9721945571203781077673167)
    ·
      refine ⟨14582918356805671616509751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9721945571203781077673167 14582918356805671616509751)
      ·
        refine ⟨21874377535208507424764627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14582918356805671616509751 21874377535208507424764627)
        ·
          refine ⟨32811566302812761137146941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21874377535208507424764627 32811566302812761137146941)
          ·
            refine ⟨12304337363554785426430103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32811566302812761137146941 12304337363554785426430103)
            ·
              refine ⟨18456506045332178139645155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12304337363554785426430103 18456506045332178139645155)
              ·
                refine ⟨27684759067998267209467733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18456506045332178139645155 27684759067998267209467733)
                ·
                  refine ⟨162215385164052346930475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27684759067998267209467733 162215385164052346930475)
                  ·
                    rfl

theorem cell23_2843220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_2843220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843220 prefixEnd_2843220 := by exact prefixLift 2843220
  have htrace : WordTrace (prefixWord ++ tailWord_2843220) baseStart_2843220 baseEnd_2843220 := by
    simpa [prefixWord, tailWord_2843220, baseEnd_2843220] using wordTrace_append hprefix tailTrace_2843220
  have hstable : (prefixWord ++ tailWord_2843220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843220).length < 2 ^ (prefixWord ++ tailWord_2843220).sum := by decide
  have hdescent : baseEnd_2843220 < baseStart_2843220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843248 : List Nat := [2, 1, 1, 1, 7, 2, 1, 2, 2, 2, 2]
def baseStart_2843248 : Nat := 118140960795 + 2843248 * 2 ^ 59
def prefixEnd_2843248 : Nat := 4983230072969 + 3 ^ 40 * 2843248 * 2
def baseEnd_2843248 : Nat := 1459952843934797012824147

theorem tailTrace_2843248 : CollatzResearch.WordTrace tailWord_2843248 prefixEnd_2843248 1459952843934797012824147 := by
  unfold tailWord_2843248
  simp only [CollatzResearch.WordTrace]
  refine ⟨51850887001702779471933199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69134516002270372629244265 51850887001702779471933199)
  ·
    refine ⟨77776330502554169207899799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51850887001702779471933199 77776330502554169207899799)
    ·
      refine ⟨116664495753831253811849699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77776330502554169207899799 116664495753831253811849699)
      ·
        refine ⟨174996743630746880717774549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116664495753831253811849699 174996743630746880717774549)
        ·
          refine ⟨4101486178845630016822841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 174996743630746880717774549 4101486178845630016822841)
          ·
            refine ⟨3076114634134222512617131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4101486178845630016822841 3076114634134222512617131)
            ·
              refine ⟨4614171951201333768925697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3076114634134222512617131 4614171951201333768925697)
              ·
                refine ⟨3460628963401000326694273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4614171951201333768925697 3460628963401000326694273)
                ·
                  refine ⟨2595471722550750245020705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3460628963401000326694273 2595471722550750245020705)
                  ·
                    refine ⟨1946603791913062683765529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2595471722550750245020705 1946603791913062683765529)
                    ·
                      refine ⟨1459952843934797012824147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1946603791913062683765529 1459952843934797012824147)
                      ·
                        rfl

theorem cell23_2843248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 2, 2, 2].length) (baseStart_2843248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843248 prefixEnd_2843248 := by exact prefixLift 2843248
  have htrace : WordTrace (prefixWord ++ tailWord_2843248) baseStart_2843248 baseEnd_2843248 := by
    simpa [prefixWord, tailWord_2843248, baseEnd_2843248] using wordTrace_append hprefix tailTrace_2843248
  have hstable : (prefixWord ++ tailWord_2843248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843248).length < 2 ^ (prefixWord ++ tailWord_2843248).sum := by decide
  have hdescent : baseEnd_2843248 < baseStart_2843248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843254 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_2843254 : Nat := 118140960795 + 2843254 * 2 ^ 59
def prefixEnd_2843254 : Nat := 4983230072969 + 3 ^ 40 * 2843254 * 2
def baseEnd_2843254 : Nat := 162217324979858221038791

theorem tailTrace_2843254 : CollatzResearch.WordTrace tailWord_2843254 prefixEnd_2843254 162217324979858221038791 := by
  unfold tailWord_2843254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6481374552586488873036551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69134661894255881312389877 6481374552586488873036551)
  ·
    refine ⟨9722061828879733309554827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6481374552586488873036551 9722061828879733309554827)
    ·
      refine ⟨14583092743319599964332241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9722061828879733309554827 14583092743319599964332241)
      ·
        refine ⟨10937319557489699973249181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14583092743319599964332241 10937319557489699973249181)
        ·
          refine ⟨4101494834058637489968443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10937319557489699973249181 4101494834058637489968443)
          ·
            refine ⟨6152242251087956234952665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101494834058637489968443 6152242251087956234952665)
            ·
              refine ⟨4614181688315967176214499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6152242251087956234952665 4614181688315967176214499)
              ·
                refine ⟨6921272532473950764321749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4614181688315967176214499 6921272532473950764321749)
                ·
                  refine ⟨162217324979858221038791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6921272532473950764321749 162217324979858221038791)
                  ·
                    rfl

theorem cell23_2843254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_2843254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843254 prefixEnd_2843254 := by exact prefixLift 2843254
  have htrace : WordTrace (prefixWord ++ tailWord_2843254) baseStart_2843254 baseEnd_2843254 := by
    simpa [prefixWord, tailWord_2843254, baseEnd_2843254] using wordTrace_append hprefix tailTrace_2843254
  have hstable : (prefixWord ++ tailWord_2843254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843254).length < 2 ^ (prefixWord ++ tailWord_2843254).sum := by decide
  have hdescent : baseEnd_2843254 < baseStart_2843254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843260 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_2843260 : Nat := 118140960795 + 2843260 * 2 ^ 59
def prefixEnd_2843260 : Nat := 4983230072969 + 3 ^ 40 * 2843260 * 2
def baseEnd_2843260 : Nat := 1459959005702650965874091

theorem tailTrace_2843260 : CollatzResearch.WordTrace tailWord_2843260 prefixEnd_2843260 1459959005702650965874091 := by
  unfold tailWord_2843260
  simp only [CollatzResearch.WordTrace]
  refine ⟨51851105839681042496651617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69134807786241389995535489 51851105839681042496651617)
  ·
    refine ⟨38888329379760781872488713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51851105839681042496651617 38888329379760781872488713)
    ·
      refine ⟨29166247034820586404366535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38888329379760781872488713 29166247034820586404366535)
      ·
        refine ⟨43749370552230879606549803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29166247034820586404366535 43749370552230879606549803)
        ·
          refine ⟨65624055828346319409824705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43749370552230879606549803 65624055828346319409824705)
          ·
            refine ⟨49218041871259739557368529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65624055828346319409824705 49218041871259739557368529)
            ·
              refine ⟨36913531403444804668026397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49218041871259739557368529 36913531403444804668026397)
              ·
                refine ⟨13842574276291801750509899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36913531403444804668026397 13842574276291801750509899)
                ·
                  refine ⟨20763861414437702625764849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13842574276291801750509899 20763861414437702625764849)
                  ·
                    refine ⟨15572896060828276969323637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20763861414437702625764849 15572896060828276969323637)
                    ·
                      refine ⟨1459959005702650965874091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15572896060828276969323637 1459959005702650965874091)
                      ·
                        rfl

theorem cell23_2843260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_2843260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843260 prefixEnd_2843260 := by exact prefixLift 2843260
  have htrace : WordTrace (prefixWord ++ tailWord_2843260) baseStart_2843260 baseEnd_2843260 := by
    simpa [prefixWord, tailWord_2843260, baseEnd_2843260] using wordTrace_append hprefix tailTrace_2843260
  have hstable : (prefixWord ++ tailWord_2843260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843260).length < 2 ^ (prefixWord ++ tailWord_2843260).sum := by decide
  have hdescent : baseEnd_2843260 < baseStart_2843260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843287 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_2843287 : Nat := 118140960795 + 2843287 * 2 ^ 59
def prefixEnd_2843287 : Nat := 4983230072969 + 3 ^ 40 * 2843287 * 2
def baseEnd_2843287 : Nat := 1459972869680322360236467

theorem tailTrace_2843287 : CollatzResearch.WordTrace tailWord_2843287 prefixEnd_2843287 1459972869680322360236467 := by
  unfold tailWord_2843287
  simp only [CollatzResearch.WordTrace]
  refine ⟨103703196450264268604536115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69135464300176179069690743 103703196450264268604536115)
  ·
    refine ⟨155554794675396402906804173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103703196450264268604536115 155554794675396402906804173)
    ·
      refine ⟨58333048003273651090051565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155554794675396402906804173 58333048003273651090051565)
      ·
        refine ⟨21874893001227619158769337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58333048003273651090051565 21874893001227619158769337)
        ·
          refine ⟨16406169750920714369077003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21874893001227619158769337 16406169750920714369077003)
          ·
            refine ⟨24609254626381071553615505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16406169750920714369077003 24609254626381071553615505)
            ·
              refine ⟨18456940969785803665211629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24609254626381071553615505 18456940969785803665211629)
              ·
                refine ⟨6921352863669676374454361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18456940969785803665211629 6921352863669676374454361)
                ·
                  refine ⟨5191014647752257280840771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6921352863669676374454361 5191014647752257280840771)
                  ·
                    refine ⟨7786521971628385921261157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5191014647752257280840771 7786521971628385921261157)
                    ·
                      refine ⟨1459972869680322360236467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7786521971628385921261157 1459972869680322360236467)
                      ·
                        rfl

theorem cell23_2843287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_2843287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843287 prefixEnd_2843287 := by exact prefixLift 2843287
  have htrace : WordTrace (prefixWord ++ tailWord_2843287) baseStart_2843287 baseEnd_2843287 := by
    simpa [prefixWord, tailWord_2843287, baseEnd_2843287] using wordTrace_append hprefix tailTrace_2843287
  have hstable : (prefixWord ++ tailWord_2843287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843287).length < 2 ^ (prefixWord ++ tailWord_2843287).sum := by decide
  have hdescent : baseEnd_2843287 < baseStart_2843287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843327 : List Nat := [1, 1, 2, 2, 2, 5, 1, 3, 6]
def baseStart_2843327 : Nat := 118140960795 + 2843327 * 2 ^ 59
def prefixEnd_2843327 : Nat := 4983230072969 + 3 ^ 40 * 2843327 * 2
def baseEnd_2843327 : Nat := 162221489878500244859587

theorem tailTrace_2843327 : CollatzResearch.WordTrace tailWord_2843327 prefixEnd_2843327 162221489878500244859587 := by
  unfold tailWord_2843327
  simp only [CollatzResearch.WordTrace]
  refine ⟨103704655370119355435992235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69136436913412903623994823 103704655370119355435992235)
  ·
    refine ⟨155556983055179033153988353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103704655370119355435992235 155556983055179033153988353)
    ·
      refine ⟨116667737291384274865491265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155556983055179033153988353 116667737291384274865491265)
      ·
        refine ⟨87500802968538206149118449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116667737291384274865491265 87500802968538206149118449)
        ·
          refine ⟨65625602226403654611838837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87500802968538206149118449 65625602226403654611838837)
          ·
            refine ⟨6152400208725342619859891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65625602226403654611838837 6152400208725342619859891)
            ·
              refine ⟨9228600313088013929789837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6152400208725342619859891 9228600313088013929789837)
              ·
                refine ⟨3460725117408005223671189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9228600313088013929789837 3460725117408005223671189)
                ·
                  refine ⟨162221489878500244859587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3460725117408005223671189 162221489878500244859587)
                  ·
                    rfl

theorem cell23_2843327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 6].length) (baseStart_2843327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843327 prefixEnd_2843327 := by exact prefixLift 2843327
  have htrace : WordTrace (prefixWord ++ tailWord_2843327) baseStart_2843327 baseEnd_2843327 := by
    simpa [prefixWord, tailWord_2843327, baseEnd_2843327] using wordTrace_append hprefix tailTrace_2843327
  have hstable : (prefixWord ++ tailWord_2843327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843327).length < 2 ^ (prefixWord ++ tailWord_2843327).sum := by decide
  have hdescent : baseEnd_2843327 < baseStart_2843327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843377 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_2843377 : Nat := 118140960795 + 2843377 * 2 ^ 59
def prefixEnd_2843377 : Nat := 4983230072969 + 3 ^ 40 * 2843377 * 2
def baseEnd_2843377 : Nat := 1460019082939227008111053

theorem tailTrace_2843377 : CollatzResearch.WordTrace tailWord_2843377 prefixEnd_2843377 1460019082939227008111053 := by
  unfold tailWord_2843377
  simp only [CollatzResearch.WordTrace]
  refine ⟨103706479019938213975312385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69137652679958809316874923 103706479019938213975312385)
  ·
    refine ⟨77779859264953660481484289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103706479019938213975312385 77779859264953660481484289)
    ·
      refine ⟨58334894448715245361113217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77779859264953660481484289 58334894448715245361113217)
      ·
        refine ⟨43751170836536434020834913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58334894448715245361113217 43751170836536434020834913)
        ·
          refine ⟨32813378127402325515626185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43751170836536434020834913 32813378127402325515626185)
          ·
            refine ⟨24610033595551744136719639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32813378127402325515626185 24610033595551744136719639)
            ·
              refine ⟨36915050393327616205079459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24610033595551744136719639 36915050393327616205079459)
              ·
                refine ⟨55372575589991424307619189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36915050393327616205079459 55372575589991424307619189)
                ·
                  refine ⟨5191178961561696028839299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55372575589991424307619189 5191178961561696028839299)
                  ·
                    refine ⟨7786768442342544043258949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5191178961561696028839299 7786768442342544043258949)
                    ·
                      refine ⟨1460019082939227008111053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7786768442342544043258949 1460019082939227008111053)
                      ·
                        rfl

theorem cell23_2843377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_2843377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843377 prefixEnd_2843377 := by exact prefixLift 2843377
  have htrace : WordTrace (prefixWord ++ tailWord_2843377) baseStart_2843377 baseEnd_2843377 := by
    simpa [prefixWord, tailWord_2843377, baseEnd_2843377] using wordTrace_append hprefix tailTrace_2843377
  have hstable : (prefixWord ++ tailWord_2843377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843377).length < 2 ^ (prefixWord ++ tailWord_2843377).sum := by decide
  have hdescent : baseEnd_2843377 < baseStart_2843377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843407 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 4]
def baseStart_2843407 : Nat := 118140960795 + 2843407 * 2 ^ 59
def prefixEnd_2843407 : Nat := 4983230072969 + 3 ^ 40 * 2843407 * 2
def baseEnd_2843407 : Nat := 1460034487358861890735915

theorem tailTrace_2843407 : CollatzResearch.WordTrace tailWord_2843407 prefixEnd_2843407 1460034487358861890735915 := by
  unfold tailWord_2843407
  simp only [CollatzResearch.WordTrace]
  refine ⟨103707573209829529098904475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69138382139886352732602983 103707573209829529098904475)
  ·
    refine ⟨155561359814744293648356713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103707573209829529098904475 155561359814744293648356713)
    ·
      refine ⟨116671019861058220236267535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155561359814744293648356713 116671019861058220236267535)
      ·
        refine ⟨175006529791587330354401303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116671019861058220236267535 175006529791587330354401303)
        ·
          refine ⟨262509794687380995531601955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175006529791587330354401303 262509794687380995531601955)
          ·
            refine ⟨393764692031071493297402933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262509794687380995531601955 393764692031071493297402933)
            ·
              refine ⟨36915439877912952496631525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 393764692031071493297402933 36915439877912952496631525)
              ·
                refine ⟨6921644977108678593118411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36915439877912952496631525 6921644977108678593118411)
                ·
                  refine ⟨10382467465663017889677617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6921644977108678593118411 10382467465663017889677617)
                  ·
                    refine ⟨7786850599247263417258213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10382467465663017889677617 7786850599247263417258213)
                    ·
                      refine ⟨1460034487358861890735915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7786850599247263417258213 1460034487358861890735915)
                      ·
                        rfl

theorem cell23_2843407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_2843407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843407 prefixEnd_2843407 := by exact prefixLift 2843407
  have htrace : WordTrace (prefixWord ++ tailWord_2843407) baseStart_2843407 baseEnd_2843407 := by
    simpa [prefixWord, tailWord_2843407, baseEnd_2843407] using wordTrace_append hprefix tailTrace_2843407
  have hstable : (prefixWord ++ tailWord_2843407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843407).length < 2 ^ (prefixWord ++ tailWord_2843407).sum := by decide
  have hdescent : baseEnd_2843407 < baseStart_2843407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843487 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 5]
def baseStart_2843487 : Nat := 118140960795 + 2843487 * 2 ^ 59
def prefixEnd_2843487 : Nat := 4983230072969 + 3 ^ 40 * 2843487 * 2
def baseEnd_2843487 : Nat := 1460075565811221577735547

theorem tailTrace_2843487 : CollatzResearch.WordTrace tailWord_2843487 prefixEnd_2843487 1460075565811221577735547 := by
  unfold tailWord_2843487
  simp only [CollatzResearch.WordTrace]
  refine ⟨103710491049539702761816715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69140327366359801841211143 103710491049539702761816715)
  ·
    refine ⟨155565736574309554142725073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103710491049539702761816715 155565736574309554142725073)
    ·
      refine ⟨116674302430732165607043805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155565736574309554142725073 116674302430732165607043805)
      ·
        refine ⟨43752863411524562102641427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116674302430732165607043805 43752863411524562102641427)
        ·
          refine ⟨65629295117286843153962141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43752863411524562102641427 65629295117286843153962141)
          ·
            refine ⟨24610985668982566182735803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65629295117286843153962141 24610985668982566182735803)
            ·
              refine ⟨36916478503473849274103705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24610985668982566182735803 36916478503473849274103705)
              ·
                refine ⟨27687358877605386955577779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36916478503473849274103705 27687358877605386955577779)
                ·
                  refine ⟨41531038316408080433366669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27687358877605386955577779 41531038316408080433366669)
                  ·
                    refine ⟨15574139368653030162512501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41531038316408080433366669 15574139368653030162512501)
                    ·
                      refine ⟨1460075565811221577735547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15574139368653030162512501 1460075565811221577735547)
                      ·
                        rfl

theorem cell23_2843487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_2843487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843487 prefixEnd_2843487 := by exact prefixLift 2843487
  have htrace : WordTrace (prefixWord ++ tailWord_2843487) baseStart_2843487 baseEnd_2843487 := by
    simpa [prefixWord, tailWord_2843487, baseEnd_2843487] using wordTrace_append hprefix tailTrace_2843487
  have hstable : (prefixWord ++ tailWord_2843487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843487).length < 2 ^ (prefixWord ++ tailWord_2843487).sum := by decide
  have hdescent : baseEnd_2843487 < baseStart_2843487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843495 : List Nat := [1, 1, 5, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_2843495 : Nat := 118140960795 + 2843495 * 2 ^ 59
def prefixEnd_2843495 : Nat := 4983230072969 + 3 ^ 40 * 2843495 * 2
def baseEnd_2843495 : Nat := 1460079673656457546435511

theorem tailTrace_2843495 : CollatzResearch.WordTrace tailWord_2843495 prefixEnd_2843495 1460079673656457546435511 := by
  unfold tailWord_2843495
  simp only [CollatzResearch.WordTrace]
  refine ⟨103710782833510720128107939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69140521889007146752071959 103710782833510720128107939)
  ·
    refine ⟨155566174250266080192161909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103710782833510720128107939 155566174250266080192161909)
    ·
      refine ⟨14584328835962445018015179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155566174250266080192161909 14584328835962445018015179)
      ·
        refine ⟨21876493253943667527022769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14584328835962445018015179 21876493253943667527022769)
        ·
          refine ⟨16407369940457750645267077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21876493253943667527022769 16407369940457750645267077)
          ·
            refine ⟨3076381863835828245987577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16407369940457750645267077 3076381863835828245987577)
            ·
              refine ⟨2307286397876871184490683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3076381863835828245987577 2307286397876871184490683)
              ·
                refine ⟨3460929596815306776736025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2307286397876871184490683 3460929596815306776736025)
                ·
                  refine ⟨2595697197611480082552019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3460929596815306776736025 2595697197611480082552019)
                  ·
                    refine ⟨3893545796417220123828029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2595697197611480082552019 3893545796417220123828029)
                    ·
                      refine ⟨1460079673656457546435511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3893545796417220123828029 1460079673656457546435511)
                      ·
                        rfl

theorem cell23_2843495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_2843495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843495 prefixEnd_2843495 := by exact prefixLift 2843495
  have htrace : WordTrace (prefixWord ++ tailWord_2843495) baseStart_2843495 baseEnd_2843495 := by
    simpa [prefixWord, tailWord_2843495, baseEnd_2843495] using wordTrace_append hprefix tailTrace_2843495
  have hstable : (prefixWord ++ tailWord_2843495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843495).length < 2 ^ (prefixWord ++ tailWord_2843495).sum := by decide
  have hdescent : baseEnd_2843495 < baseStart_2843495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843501 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_2843501 : Nat := 118140960795 + 2843501 * 2 ^ 59
def prefixEnd_2843501 : Nat := 4983230072969 + 3 ^ 40 * 2843501 * 2
def baseEnd_2843501 : Nat := 1460082754540384522960483

theorem tailTrace_2843501 : CollatzResearch.WordTrace tailWord_2843501 prefixEnd_2843501 1460082754540384522960483 := by
  unfold tailWord_2843501
  simp only [CollatzResearch.WordTrace]
  refine ⟨103711001671488983152826357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69140667780992655435217571 103711001671488983152826357)
  ·
    refine ⟨9722906406702092170577471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103711001671488983152826357 9722906406702092170577471)
    ·
      refine ⟨14584359610053138255866207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9722906406702092170577471 14584359610053138255866207)
      ·
        refine ⟨21876539415079707383799311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14584359610053138255866207 21876539415079707383799311)
        ·
          refine ⟨32814809122619561075698967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21876539415079707383799311 32814809122619561075698967)
          ·
            refine ⟨49222213683929341613548451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32814809122619561075698967 49222213683929341613548451)
            ·
              refine ⟨73833320525894012420322677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49222213683929341613548451 73833320525894012420322677)
              ·
                refine ⟨6921873799302563664405251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73833320525894012420322677 6921873799302563664405251)
                ·
                  refine ⟨10382810698953845496607877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6921873799302563664405251 10382810698953845496607877)
                  ·
                    refine ⟨1946777006053846030613977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10382810698953845496607877 1946777006053846030613977)
                    ·
                      refine ⟨1460082754540384522960483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1946777006053846030613977 1460082754540384522960483)
                      ·
                        rfl

theorem cell23_2843501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_2843501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843501 prefixEnd_2843501 := by exact prefixLift 2843501
  have htrace : WordTrace (prefixWord ++ tailWord_2843501) baseStart_2843501 baseEnd_2843501 := by
    simpa [prefixWord, tailWord_2843501, baseEnd_2843501] using wordTrace_append hprefix tailTrace_2843501
  have hstable : (prefixWord ++ tailWord_2843501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843501).length < 2 ^ (prefixWord ++ tailWord_2843501).sum := by decide
  have hdescent : baseEnd_2843501 < baseStart_2843501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843507 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 7]
def baseStart_2843507 : Nat := 118140960795 + 2843507 * 2 ^ 59
def prefixEnd_2843507 : Nat := 4983230072969 + 3 ^ 40 * 2843507 * 2
def baseEnd_2843507 : Nat := 162231759491590166609495

theorem tailTrace_2843507 : CollatzResearch.WordTrace tailWord_2843507 prefixEnd_2843507 162231759491590166609495 := by
  unfold tailWord_2843507
  simp only [CollatzResearch.WordTrace]
  refine ⟨103711220509467246177544775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69140813672978164118363183 103711220509467246177544775)
  ·
    refine ⟨155566830764200869266317163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103711220509467246177544775 155566830764200869266317163)
    ·
      refine ⟨233350246146301303899475745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155566830764200869266317163 233350246146301303899475745)
      ·
        refine ⟨175012684609725977924606809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233350246146301303899475745 175012684609725977924606809)
        ·
          refine ⟨131259513457294483443455107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175012684609725977924606809 131259513457294483443455107)
          ·
            refine ⟨196889270185941725165182661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131259513457294483443455107 196889270185941725165182661)
            ·
              refine ⟨36916738159864073468471749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196889270185941725165182661 36916738159864073468471749)
              ·
                refine ⟨6921888404974513775338453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36916738159864073468471749 6921888404974513775338453)
                ·
                  refine ⟨162231759491590166609495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6921888404974513775338453 162231759491590166609495)
                  ·
                    rfl

theorem cell23_2843507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 7].length) (baseStart_2843507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843507 prefixEnd_2843507 := by exact prefixLift 2843507
  have htrace : WordTrace (prefixWord ++ tailWord_2843507) baseStart_2843507 baseEnd_2843507 := by
    simpa [prefixWord, tailWord_2843507, baseEnd_2843507] using wordTrace_append hprefix tailTrace_2843507
  have hstable : (prefixWord ++ tailWord_2843507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843507).length < 2 ^ (prefixWord ++ tailWord_2843507).sum := by decide
  have hdescent : baseEnd_2843507 < baseStart_2843507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843537 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 3, 7]
def baseStart_2843537 : Nat := 118140960795 + 2843537 * 2 ^ 59
def prefixEnd_2843537 : Nat := 4983230072969 + 3 ^ 40 * 2843537 * 2
def baseEnd_2843537 : Nat := 486700413281315460703439

theorem tailTrace_2843537 : CollatzResearch.WordTrace tailWord_2843537 prefixEnd_2843537 486700413281315460703439 := by
  unfold tailWord_2843537
  simp only [CollatzResearch.WordTrace]
  refine ⟨103712314699358561301136865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69141543132905707534091243 103712314699358561301136865)
  ·
    refine ⟨77784236024518920975852649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103712314699358561301136865 77784236024518920975852649)
    ·
      refine ⟨58338177018389190731889487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77784236024518920975852649 58338177018389190731889487)
      ·
        refine ⟨87507265527583786097834231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58338177018389190731889487 87507265527583786097834231)
        ·
          refine ⟨131260898291375679146751347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87507265527583786097834231 131260898291375679146751347)
          ·
            refine ⟨196891347437063518720127021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131260898291375679146751347 196891347437063518720127021)
            ·
              refine ⟨73834255288898819520047633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196891347437063518720127021 73834255288898819520047633)
              ·
                refine ⟨55375691466674114640035725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73834255288898819520047633 55375691466674114640035725)
                ·
                  refine ⟨20765884300002792990013397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55375691466674114640035725 20765884300002792990013397)
                  ·
                    refine ⟨486700413281315460703439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20765884300002792990013397 486700413281315460703439)
                    ·
                      rfl

theorem cell23_2843537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_2843537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843537 prefixEnd_2843537 := by exact prefixLift 2843537
  have htrace : WordTrace (prefixWord ++ tailWord_2843537) baseStart_2843537 baseEnd_2843537 := by
    simpa [prefixWord, tailWord_2843537, baseEnd_2843537] using wordTrace_append hprefix tailTrace_2843537
  have hstable : (prefixWord ++ tailWord_2843537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843537).length < 2 ^ (prefixWord ++ tailWord_2843537).sum := by decide
  have hdescent : baseEnd_2843537 < baseStart_2843537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843541 : List Nat := [1, 3, 2, 1, 1, 5, 1, 4, 5]
def baseStart_2843541 : Nat := 118140960795 + 2843541 * 2 ^ 59
def prefixEnd_2843541 : Nat := 4983230072969 + 3 ^ 40 * 2843541 * 2
def baseEnd_2843541 : Nat := 162233699307396040717811

theorem tailTrace_2843541 : CollatzResearch.WordTrace tailWord_2843541 prefixEnd_2843541 162233699307396040717811 := by
  unfold tailWord_2843541
  simp only [CollatzResearch.WordTrace]
  refine ⟨103712460591344069984282477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69141640394229379989521651 103712460591344069984282477)
  ·
    refine ⟨38892172721754026244105929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103712460591344069984282477 38892172721754026244105929)
    ·
      refine ⟨29169129541315519683079447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38892172721754026244105929 29169129541315519683079447)
      ·
        refine ⟨43753694311973279524619171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29169129541315519683079447 43753694311973279524619171)
        ·
          refine ⟨65630541467959919286928757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43753694311973279524619171 65630541467959919286928757)
          ·
            refine ⟨6152863262621242433149571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65630541467959919286928757 6152863262621242433149571)
            ·
              refine ⟨9229294893931863649724357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6152863262621242433149571 9229294893931863649724357)
              ·
                refine ⟨1730492792612224434323317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9229294893931863649724357 1730492792612224434323317)
                ·
                  refine ⟨162233699307396040717811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1730492792612224434323317 162233699307396040717811)
                  ·
                    rfl

theorem cell23_2843541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 5].length) (baseStart_2843541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843541 prefixEnd_2843541 := by exact prefixLift 2843541
  have htrace : WordTrace (prefixWord ++ tailWord_2843541) baseStart_2843541 baseEnd_2843541 := by
    simpa [prefixWord, tailWord_2843541, baseEnd_2843541] using wordTrace_append hprefix tailTrace_2843541
  have hstable : (prefixWord ++ tailWord_2843541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843541).length < 2 ^ (prefixWord ++ tailWord_2843541).sum := by decide
  have hdescent : baseEnd_2843541 < baseStart_2843541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843551 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 3]
def baseStart_2843551 : Nat := 118140960795 + 2843551 * 2 ^ 59
def prefixEnd_2843551 : Nat := 4983230072969 + 3 ^ 40 * 2843551 * 2
def baseEnd_2843551 : Nat := 1460108428573109327335253

theorem tailTrace_2843551 : CollatzResearch.WordTrace tailWord_2843551 prefixEnd_2843551 1460108428573109327335253 := by
  unfold tailWord_2843551
  simp only [CollatzResearch.WordTrace]
  refine ⟨103712825321307841692146507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69141883547538561128097671 103712825321307841692146507)
  ·
    refine ⟨155569237981961762538219761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103712825321307841692146507 155569237981961762538219761)
    ·
      refine ⟨116676928486471321903664821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155569237981961762538219761 116676928486471321903664821)
      ·
        refine ⟨10938462045606686428468577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116676928486471321903664821 10938462045606686428468577)
        ·
          refine ⟨8203846534205014821351433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10938462045606686428468577 8203846534205014821351433)
          ·
            refine ⟨6152884900653761116013575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8203846534205014821351433 6152884900653761116013575)
            ·
              refine ⟨9229327350980641674020363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6152884900653761116013575 9229327350980641674020363)
              ·
                refine ⟨13843991026470962511030545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9229327350980641674020363 13843991026470962511030545)
                ·
                  refine ⟨10382993269853221883272909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13843991026470962511030545 10382993269853221883272909)
                  ·
                    refine ⟨3893622476194958206227341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10382993269853221883272909 3893622476194958206227341)
                    ·
                      refine ⟨1460108428573109327335253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3893622476194958206227341 1460108428573109327335253)
                      ·
                        rfl

theorem cell23_2843551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_2843551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843551 prefixEnd_2843551 := by exact prefixLift 2843551
  have htrace : WordTrace (prefixWord ++ tailWord_2843551) baseStart_2843551 baseEnd_2843551 := by
    simpa [prefixWord, tailWord_2843551, baseEnd_2843551] using wordTrace_append hprefix tailTrace_2843551
  have hstable : (prefixWord ++ tailWord_2843551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843551).length < 2 ^ (prefixWord ++ tailWord_2843551).sum := by decide
  have hdescent : baseEnd_2843551 < baseStart_2843551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843567 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 1, 10]
def baseStart_2843567 : Nat := 118140960795 + 2843567 * 2 ^ 59
def prefixEnd_2843567 : Nat := 4983230072969 + 3 ^ 40 * 2843567 * 2
def baseEnd_2843567 : Nat := 486705548087860421578393

theorem tailTrace_2843567 : CollatzResearch.WordTrace tailWord_2843567 prefixEnd_2843567 486705548087860421578393 := by
  unfold tailWord_2843567
  simp only [CollatzResearch.WordTrace]
  refine ⟨103713408889249876424728955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69142272592833250949819303 103713408889249876424728955)
  ·
    refine ⟨155570113333874814637093433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103713408889249876424728955 155570113333874814637093433)
    ·
      refine ⟨116677585000406110977820075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155570113333874814637093433 116677585000406110977820075)
      ·
        refine ⟨175016377500609166466730113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116677585000406110977820075 175016377500609166466730113)
        ·
          refine ⟨131262283125456874850047585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175016377500609166466730113 131262283125456874850047585)
          ·
            refine ⟨98446712344092656137535689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131262283125456874850047585 98446712344092656137535689)
            ·
              refine ⟨73835034258069492103151767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98446712344092656137535689 73835034258069492103151767)
              ·
                refine ⟨110752551387104238154727651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73835034258069492103151767 110752551387104238154727651)
                ·
                  refine ⟨166128827080656357232091477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110752551387104238154727651 166128827080656357232091477)
                  ·
                    refine ⟨486705548087860421578393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 166128827080656357232091477 486705548087860421578393)
                    ·
                      rfl

theorem cell23_2843567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_2843567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843567 prefixEnd_2843567 := by exact prefixLift 2843567
  have htrace : WordTrace (prefixWord ++ tailWord_2843567) baseStart_2843567 baseEnd_2843567 := by
    simpa [prefixWord, tailWord_2843567, baseEnd_2843567] using wordTrace_append hprefix tailTrace_2843567
  have hstable : (prefixWord ++ tailWord_2843567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843567).length < 2 ^ (prefixWord ++ tailWord_2843567).sum := by decide
  have hdescent : baseEnd_2843567 < baseStart_2843567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843591 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 2, 4, 2]
def baseStart_2843591 : Nat := 118140960795 + 2843591 * 2 ^ 59
def prefixEnd_2843591 : Nat := 4983230072969 + 3 ^ 40 * 2843591 * 2
def baseEnd_2843591 : Nat := 1460128967799289170835069

theorem tailTrace_2843591 : CollatzResearch.WordTrace tailWord_2843591 prefixEnd_2843591 1460128967799289170835069 := by
  unfold tailWord_2843591
  simp only [CollatzResearch.WordTrace]
  refine ⟨103714284241162928523602627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69142856160775285682401751 103714284241162928523602627)
  ·
    refine ⟨155571426361744392785403941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103714284241162928523602627 155571426361744392785403941)
    ·
      refine ⟨29169642442827073647263239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155571426361744392785403941 29169642442827073647263239)
      ·
        refine ⟨43754463664240610470894859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29169642442827073647263239 43754463664240610470894859)
        ·
          refine ⟨65631695496360915706342289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43754463664240610470894859 65631695496360915706342289)
          ·
            refine ⟨49223771622270686779756717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65631695496360915706342289 49223771622270686779756717)
            ·
              refine ⟨18458914358351507542408769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49223771622270686779756717 18458914358351507542408769)
              ·
                refine ⟨13844185768763630656806577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18458914358351507542408769 13844185768763630656806577)
                ·
                  refine ⟨10383139326572722992604933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13844185768763630656806577 10383139326572722992604933)
                  ·
                    refine ⟨1946838623732385561113425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10383139326572722992604933 1946838623732385561113425)
                    ·
                      refine ⟨1460128967799289170835069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1946838623732385561113425 1460128967799289170835069)
                      ·
                        rfl

theorem cell23_2843591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_2843591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843591 prefixEnd_2843591 := by exact prefixLift 2843591
  have htrace : WordTrace (prefixWord ++ tailWord_2843591) baseStart_2843591 baseEnd_2843591 := by
    simpa [prefixWord, tailWord_2843591, baseEnd_2843591] using wordTrace_append hprefix tailTrace_2843591
  have hstable : (prefixWord ++ tailWord_2843591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843591).length < 2 ^ (prefixWord ++ tailWord_2843591).sum := by decide
  have hdescent : baseEnd_2843591 < baseStart_2843591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843601 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 3, 4]
def baseStart_2843601 : Nat := 118140960795 + 2843601 * 2 ^ 59
def prefixEnd_2843601 : Nat := 4983230072969 + 3 ^ 40 * 2843601 * 2
def baseEnd_2843601 : Nat := 486711367535278043903341

theorem tailTrace_2843601 : CollatzResearch.WordTrace tailWord_2843601 prefixEnd_2843601 486711367535278043903341 := by
  unfold tailWord_2843601
  simp only [CollatzResearch.WordTrace]
  refine ⟨103714648971126700231466657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69143099314084466820977771 103714648971126700231466657)
  ·
    refine ⟨77785986728345025173599993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103714648971126700231466657 77785986728345025173599993)
    ·
      refine ⟨58339490046258768880199995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77785986728345025173599993 58339490046258768880199995)
      ·
        refine ⟨87509235069388153320299993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58339490046258768880199995 87509235069388153320299993)
        ·
          refine ⟨65631926302041114990224995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87509235069388153320299993 65631926302041114990224995)
          ·
            refine ⟨98447889453061672485337493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65631926302041114990224995 98447889453061672485337493)
            ·
              refine ⟨4614744818112265897750195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98447889453061672485337493 4614744818112265897750195)
              ·
                refine ⟨6922117227168398846625293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4614744818112265897750195 6922117227168398846625293)
                ·
                  refine ⟨2595793960188149567484485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6922117227168398846625293 2595793960188149567484485)
                  ·
                    refine ⟨486711367535278043903341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2595793960188149567484485 486711367535278043903341)
                    ·
                      rfl

theorem cell23_2843601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_2843601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843601 prefixEnd_2843601 := by exact prefixLift 2843601
  have htrace : WordTrace (prefixWord ++ tailWord_2843601) baseStart_2843601 baseEnd_2843601 := by
    simpa [prefixWord, tailWord_2843601, baseEnd_2843601] using wordTrace_append hprefix tailTrace_2843601
  have hstable : (prefixWord ++ tailWord_2843601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843601).length < 2 ^ (prefixWord ++ tailWord_2843601).sum := by decide
  have hdescent : baseEnd_2843601 < baseStart_2843601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843704 : List Nat := [2, 1, 2, 1, 5, 12]
def baseStart_2843704 : Nat := 118140960795 + 2843704 * 2 ^ 59
def prefixEnd_2843704 : Nat := 4983230072969 + 3 ^ 40 * 2843704 * 2
def baseEnd_2843704 : Nat := 6008999963429000941243

theorem tailTrace_2843704 : CollatzResearch.WordTrace tailWord_2843704 prefixEnd_2843704 6008999963429000941243 := by
  unfold tailWord_2843704
  simp only [CollatzResearch.WordTrace]
  refine ⟨51859202844876774411233083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69145603793169032548310777 51859202844876774411233083)
  ·
    refine ⟨77788804267315161616849625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51859202844876774411233083 77788804267315161616849625)
    ·
      refine ⟨58341603200486371212637219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77788804267315161616849625 58341603200486371212637219)
      ·
        refine ⟨87512404800729556818955829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58341603200486371212637219 87512404800729556818955829)
        ·
          refine ⟨8204287950068395951777109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87512404800729556818955829 8204287950068395951777109)
          ·
            refine ⟨6008999963429000941243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8204287950068395951777109 6008999963429000941243)
            ·
              rfl

theorem cell23_2843704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 12].length) (baseStart_2843704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843704 prefixEnd_2843704 := by exact prefixLift 2843704
  have htrace : WordTrace (prefixWord ++ tailWord_2843704) baseStart_2843704 baseEnd_2843704 := by
    simpa [prefixWord, tailWord_2843704, baseEnd_2843704] using wordTrace_append hprefix tailTrace_2843704
  have hstable : (prefixWord ++ tailWord_2843704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843704).length < 2 ^ (prefixWord ++ tailWord_2843704).sum := by decide
  have hdescent : baseEnd_2843704 < baseStart_2843704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843708 : List Nat := [2, 2, 2, 2, 2, 2, 1, 4, 2, 4]
def baseStart_2843708 : Nat := 118140960795 + 2843708 * 2 ^ 59
def prefixEnd_2843708 : Nat := 4983230072969 + 3 ^ 40 * 2843708 * 2
def baseEnd_2843708 : Nat := 486729681678621737690677

theorem tailTrace_2843708 : CollatzResearch.WordTrace tailWord_2843708 prefixEnd_2843708 486729681678621737690677 := by
  unfold tailWord_2843708
  simp only [CollatzResearch.WordTrace]
  refine ⟨51859275790869528752805889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69145701054492705003741185 51859275790869528752805889)
  ·
    refine ⟨38894456843152146564604417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51859275790869528752805889 38894456843152146564604417)
    ·
      refine ⟨29170842632364109923453313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38894456843152146564604417 29170842632364109923453313)
      ·
        refine ⟨21878131974273082442589985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29170842632364109923453313 21878131974273082442589985)
        ·
          refine ⟨16408598980704811831942489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21878131974273082442589985 16408598980704811831942489)
          ·
            refine ⟨12306449235528608873956867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16408598980704811831942489 12306449235528608873956867)
            ·
              refine ⟨18459673853292913310935301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12306449235528608873956867 18459673853292913310935301)
              ·
                refine ⟨3461188847492421245800369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18459673853292913310935301 3461188847492421245800369)
                ·
                  refine ⟨2595891635619315934350277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3461188847492421245800369 2595891635619315934350277)
                  ·
                    refine ⟨486729681678621737690677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2595891635619315934350277 486729681678621737690677)
                    ·
                      rfl

theorem cell23_2843708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_2843708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843708 prefixEnd_2843708 := by exact prefixLift 2843708
  have htrace : WordTrace (prefixWord ++ tailWord_2843708) baseStart_2843708 baseEnd_2843708 := by
    simpa [prefixWord, tailWord_2843708, baseEnd_2843708] using wordTrace_append hprefix tailTrace_2843708
  have hstable : (prefixWord ++ tailWord_2843708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843708).length < 2 ^ (prefixWord ++ tailWord_2843708).sum := by decide
  have hdescent : baseEnd_2843708 < baseStart_2843708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843709 : List Nat := [1, 4, 1, 3, 1, 4, 2, 2, 1, 1, 3]
def baseStart_2843709 : Nat := 118140960795 + 2843709 * 2 ^ 59
def prefixEnd_2843709 : Nat := 4983230072969 + 3 ^ 40 * 2843709 * 2
def baseEnd_2843709 : Nat := 1460189558516519709159527

theorem tailTrace_2843709 : CollatzResearch.WordTrace tailWord_2843709 prefixEnd_2843709 1460189558516519709159527 := by
  unfold tailWord_2843709
  simp only [CollatzResearch.WordTrace]
  refine ⟨103718588054735434676398181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69145725369823623117598787 103718588054735434676398181)
  ·
    refine ⟨19447235260262894001824659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103718588054735434676398181 19447235260262894001824659)
    ·
      refine ⟨29170852890394341002736989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19447235260262894001824659 29170852890394341002736989)
      ·
        refine ⟨10939069833897877876026371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29170852890394341002736989 10939069833897877876026371)
        ·
          refine ⟨16408604750846816814039557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10939069833897877876026371 16408604750846816814039557)
          ·
            refine ⟨3076613390783778152632417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16408604750846816814039557 3076613390783778152632417)
            ·
              refine ⟨2307460043087833614474313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3076613390783778152632417 2307460043087833614474313)
              ·
                refine ⟨1730595032315875210855735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2307460043087833614474313 1730595032315875210855735)
                ·
                  refine ⟨2595892548473812816283603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1730595032315875210855735 2595892548473812816283603)
                  ·
                    refine ⟨3893838822710719224425405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2595892548473812816283603 3893838822710719224425405)
                    ·
                      refine ⟨1460189558516519709159527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3893838822710719224425405 1460189558516519709159527)
                      ·
                        rfl

theorem cell23_2843709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_2843709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843709 prefixEnd_2843709 := by exact prefixLift 2843709
  have htrace : WordTrace (prefixWord ++ tailWord_2843709) baseStart_2843709 baseEnd_2843709 := by
    simpa [prefixWord, tailWord_2843709, baseEnd_2843709] using wordTrace_append hprefix tailTrace_2843709
  have hstable : (prefixWord ++ tailWord_2843709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843709).length < 2 ^ (prefixWord ++ tailWord_2843709).sum := by decide
  have hdescent : baseEnd_2843709 < baseStart_2843709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843725 : List Nat := [1, 6, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_2843725 : Nat := 118140960795 + 2843725 * 2 ^ 59
def prefixEnd_2843725 : Nat := 4983230072969 + 3 ^ 40 * 2843725 * 2
def baseEnd_2843725 : Nat := 486732591402330548853151

theorem tailTrace_2843725 : CollatzResearch.WordTrace tailWord_2843725 prefixEnd_2843725 486732591402330548853151 := by
  unfold tailWord_2843725
  simp only [CollatzResearch.WordTrace]
  refine ⟨103719171622677469408980629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69146114415118312939320419 103719171622677469408980629)
  ·
    refine ⟨4861836169813006378545967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 103719171622677469408980629 4861836169813006378545967)
    ·
      refine ⟨7292754254719509567818951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4861836169813006378545967 7292754254719509567818951)
      ·
        refine ⟨10939131382079264351728427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7292754254719509567818951 10939131382079264351728427)
        ·
          refine ⟨16408697073118896527592641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10939131382079264351728427 16408697073118896527592641)
          ·
            refine ⟨12306522804839172395694481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16408697073118896527592641 12306522804839172395694481)
            ·
              refine ⟨9229892103629379296770861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12306522804839172395694481 9229892103629379296770861)
              ·
                refine ⟨3461209538861017236289073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9229892103629379296770861 3461209538861017236289073)
                ·
                  refine ⟨2595907154145762927216805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3461209538861017236289073 2595907154145762927216805)
                  ·
                    refine ⟨486732591402330548853151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2595907154145762927216805 486732591402330548853151)
                    ·
                      rfl

theorem cell23_2843725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_2843725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843725 prefixEnd_2843725 := by exact prefixLift 2843725
  have htrace : WordTrace (prefixWord ++ tailWord_2843725) baseStart_2843725 baseEnd_2843725 := by
    simpa [prefixWord, tailWord_2843725, baseEnd_2843725] using wordTrace_append hprefix tailTrace_2843725
  have hstable : (prefixWord ++ tailWord_2843725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843725).length < 2 ^ (prefixWord ++ tailWord_2843725).sum := by decide
  have hdescent : baseEnd_2843725 < baseStart_2843725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843731 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 3]
def baseStart_2843731 : Nat := 118140960795 + 2843731 * 2 ^ 59
def prefixEnd_2843731 : Nat := 4983230072969 + 3 ^ 40 * 2843731 * 2
def baseEnd_2843731 : Nat := 1460200855090918623084425

theorem tailTrace_2843731 : CollatzResearch.WordTrace tailWord_2843731 prefixEnd_2843731 1460200855090918623084425 := by
  unfold tailWord_2843731
  simp only [CollatzResearch.WordTrace]
  refine ⟨103719390460655732433699047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69146260307103821622466031 103719390460655732433699047)
  ·
    refine ⟨155579085690983598650548571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103719390460655732433699047 155579085690983598650548571)
    ·
      refine ⟨233368628536475397975822857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155579085690983598650548571 233368628536475397975822857)
      ·
        refine ⟨175026471402356548481867143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233368628536475397975822857 175026471402356548481867143)
        ·
          refine ⟨262539707103534822722800715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175026471402356548481867143 262539707103534822722800715)
          ·
            refine ⟨393809560655302234084201073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262539707103534822722800715 393809560655302234084201073)
            ·
              refine ⟨295357170491476675563150805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393809560655302234084201073 295357170491476675563150805)
              ·
                refine ⟨6922433683393984583511347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 295357170491476675563150805 6922433683393984583511347)
                ·
                  refine ⟨10383650525090976875267021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6922433683393984583511347 10383650525090976875267021)
                  ·
                    refine ⟨3893868946909116328225133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10383650525090976875267021 3893868946909116328225133)
                    ·
                      refine ⟨1460200855090918623084425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3893868946909116328225133 1460200855090918623084425)
                      ·
                        rfl

theorem cell23_2843731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 3].length) (baseStart_2843731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843731 prefixEnd_2843731 := by exact prefixLift 2843731
  have htrace : WordTrace (prefixWord ++ tailWord_2843731) baseStart_2843731 baseEnd_2843731 := by
    simpa [prefixWord, tailWord_2843731, baseEnd_2843731] using wordTrace_append hprefix tailTrace_2843731
  have hstable : (prefixWord ++ tailWord_2843731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843731).length < 2 ^ (prefixWord ++ tailWord_2843731).sum := by decide
  have hdescent : baseEnd_2843731 < baseStart_2843731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843748 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_2843748 : Nat := 118140960795 + 2843748 * 2 ^ 59
def prefixEnd_2843748 : Nat := 4983230072969 + 3 ^ 40 * 2843748 * 2
def baseEnd_2843748 : Nat := 1460209584262045056571847

theorem tailTrace_2843748 : CollatzResearch.WordTrace tailWord_2843748 prefixEnd_2843748 1460209584262045056571847 := by
  unfold tailWord_2843748
  simp only [CollatzResearch.WordTrace]
  refine ⟨51860005250797072168533949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69146673667729429558045265 51860005250797072168533949)
  ·
    refine ⟨19447501969048902063200231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51860005250797072168533949 19447501969048902063200231)
    ·
      refine ⟨29171252953573353094800347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19447501969048902063200231 29171252953573353094800347)
      ·
        refine ⟨43756879430360029642200521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29171252953573353094800347 43756879430360029642200521)
        ·
          refine ⟨32817659572770022231650391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43756879430360029642200521 32817659572770022231650391)
          ·
            refine ⟨49226489359155033347475587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32817659572770022231650391 49226489359155033347475587)
            ·
              refine ⟨73839734038732550021213381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49226489359155033347475587 73839734038732550021213381)
              ·
                refine ⟨13844950132262353128977509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73839734038732550021213381 13844950132262353128977509)
                ·
                  refine ⟨2595928149799191211683283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13844950132262353128977509 2595928149799191211683283)
                  ·
                    refine ⟨3893892224698786817524925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2595928149799191211683283 3893892224698786817524925)
                    ·
                      refine ⟨1460209584262045056571847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3893892224698786817524925 1460209584262045056571847)
                      ·
                        rfl

theorem cell23_2843748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_2843748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843748 prefixEnd_2843748 := by exact prefixLift 2843748
  have htrace : WordTrace (prefixWord ++ tailWord_2843748) baseStart_2843748 baseEnd_2843748 := by
    simpa [prefixWord, tailWord_2843748, baseEnd_2843748] using wordTrace_append hprefix tailTrace_2843748
  have hstable : (prefixWord ++ tailWord_2843748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843748).length < 2 ^ (prefixWord ++ tailWord_2843748).sum := by decide
  have hdescent : baseEnd_2843748 < baseStart_2843748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843752 : List Nat := [2, 1, 4, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2843752 : Nat := 118140960795 + 2843752 * 2 ^ 59
def prefixEnd_2843752 : Nat := 4983230072969 + 3 ^ 40 * 2843752 * 2
def baseEnd_2843752 : Nat := 1460211638184663040921829

theorem tailTrace_2843752 : CollatzResearch.WordTrace tailWord_2843752 prefixEnd_2843752 1460211638184663040921829 := by
  unfold tailWord_2843752
  simp only [CollatzResearch.WordTrace]
  refine ⟨51860078196789826510106755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69146770929053102013475673 51860078196789826510106755)
  ·
    refine ⟨77790117295184739765160133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51860078196789826510106755 77790117295184739765160133)
    ·
      refine ⟨14585646992847138705967525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77790117295184739765160133 14585646992847138705967525)
      ·
        refine ⟨2734808811158838507368911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14585646992847138705967525 2734808811158838507368911)
        ·
          refine ⟨4102213216738257761053367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2734808811158838507368911 4102213216738257761053367)
          ·
            refine ⟨6153319825107386641580051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4102213216738257761053367 6153319825107386641580051)
            ·
              refine ⟨9229979737661079962370077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6153319825107386641580051 9229979737661079962370077)
              ·
                refine ⟨3461242401622904985888779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9229979737661079962370077 3461242401622904985888779)
                ·
                  refine ⟨5191863602434357478833169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461242401622904985888779 5191863602434357478833169)
                  ·
                    refine ⟨3893897701825768109124877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5191863602434357478833169 3893897701825768109124877)
                    ·
                      refine ⟨1460211638184663040921829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3893897701825768109124877 1460211638184663040921829)
                      ·
                        rfl

theorem cell23_2843752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2843752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843752 prefixEnd_2843752 := by exact prefixLift 2843752
  have htrace : WordTrace (prefixWord ++ tailWord_2843752) baseStart_2843752 baseEnd_2843752 := by
    simpa [prefixWord, tailWord_2843752, baseEnd_2843752] using wordTrace_append hprefix tailTrace_2843752
  have hstable : (prefixWord ++ tailWord_2843752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843752).length < 2 ^ (prefixWord ++ tailWord_2843752).sum := by decide
  have hdescent : baseEnd_2843752 < baseStart_2843752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843805 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_2843805 : Nat := 118140960795 + 2843805 * 2 ^ 59
def prefixEnd_2843805 : Nat := 4983230072969 + 3 ^ 40 * 2843805 * 2
def baseEnd_2843805 : Nat := 1460238852659351333559085

theorem tailTrace_2843805 : CollatzResearch.WordTrace tailWord_2843805 prefixEnd_2843805 1460238852659351333559085 := by
  unfold tailWord_2843805
  simp only [CollatzResearch.WordTrace]
  refine ⟨103722089462387643071892869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69148059641591762047928579 103722089462387643071892869)
  ·
    refine ⟨19447891774197683075979913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103722089462387643071892869 19447891774197683075979913)
    ·
      refine ⟨14585918830648262306984935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19447891774197683075979913 14585918830648262306984935)
      ·
        refine ⟨21878878245972393460477403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14585918830648262306984935 21878878245972393460477403)
        ·
          refine ⟨32818317368958590190716105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21878878245972393460477403 32818317368958590190716105)
          ·
            refine ⟨24613738026718942643037079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32818317368958590190716105 24613738026718942643037079)
            ·
              refine ⟨36920607040078413964555619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24613738026718942643037079 36920607040078413964555619)
              ·
                refine ⟨55380910560117620946833429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36920607040078413964555619 55380910560117620946833429)
                ·
                  refine ⟨2595980182505513481882817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55380910560117620946833429 2595980182505513481882817)
                  ·
                    refine ⟨1946985136879135111412113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2595980182505513481882817 1946985136879135111412113)
                    ·
                      refine ⟨1460238852659351333559085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1946985136879135111412113 1460238852659351333559085)
                      ·
                        rfl

theorem cell23_2843805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_2843805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843805 prefixEnd_2843805 := by exact prefixLift 2843805
  have htrace : WordTrace (prefixWord ++ tailWord_2843805) baseStart_2843805 baseEnd_2843805 := by
    simpa [prefixWord, tailWord_2843805, baseEnd_2843805] using wordTrace_append hprefix tailTrace_2843805
  have hstable : (prefixWord ++ tailWord_2843805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843805).length < 2 ^ (prefixWord ++ tailWord_2843805).sum := by decide
  have hdescent : baseEnd_2843805 < baseStart_2843805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843879 : List Nat := [1, 1, 5, 3, 2, 2, 2, 2, 5]
def baseStart_2843879 : Nat := 118140960795 + 2843879 * 2 ^ 59
def prefixEnd_2843879 : Nat := 4983230072969 + 3 ^ 40 * 2843879 * 2
def baseEnd_2843879 : Nat := 162252983358642671559305

theorem tailTrace_2843879 : CollatzResearch.WordTrace tailWord_2843879 prefixEnd_2843879 162252983358642671559305 := by
  unfold tailWord_2843879
  simp only [CollatzResearch.WordTrace]
  refine ⟨103724788464119553710086691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69149858976079702473391127 103724788464119553710086691)
  ·
    refine ⟨155587182696179330565130037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103724788464119553710086691 155587182696179330565130037)
    ·
      refine ⟨14586298377766812240480941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155587182696179330565130037 14586298377766812240480941)
      ·
        refine ⟨5469861891662554590180353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14586298377766812240480941 5469861891662554590180353)
        ·
          refine ⟨4102396418746915942635265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5469861891662554590180353 4102396418746915942635265)
          ·
            refine ⟨3076797314060186956976449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4102396418746915942635265 3076797314060186956976449)
            ·
              refine ⟨2307597985545140217732337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3076797314060186956976449 2307597985545140217732337)
              ·
                refine ⟨1730698489158855163299253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2307597985545140217732337 1730698489158855163299253)
                ·
                  refine ⟨162252983358642671559305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1730698489158855163299253 162252983358642671559305)
                  ·
                    rfl

theorem cell23_2843879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 5].length) (baseStart_2843879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843879 prefixEnd_2843879 := by exact prefixLift 2843879
  have htrace : WordTrace (prefixWord ++ tailWord_2843879) baseStart_2843879 baseEnd_2843879 := by
    simpa [prefixWord, tailWord_2843879, baseEnd_2843879] using wordTrace_append hprefix tailTrace_2843879
  have hstable : (prefixWord ++ tailWord_2843879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843879).length < 2 ^ (prefixWord ++ tailWord_2843879).sum := by decide
  have hdescent : baseEnd_2843879 < baseStart_2843879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843898 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3]
def baseStart_2843898 : Nat := 118140960795 + 2843898 * 2 ^ 59
def prefixEnd_2843898 : Nat := 4983230072969 + 3 ^ 40 * 2843898 * 2
def baseEnd_2843898 : Nat := 1460286606360219469696157

theorem tailTrace_2843898 : CollatzResearch.WordTrace tailWord_2843898 prefixEnd_2843898 1460286606360219469696157 := by
  unfold tailWord_2843898
  simp only [CollatzResearch.WordTrace]
  refine ⟨25931370362762679988757087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69150320967367146636685565 25931370362762679988757087)
  ·
    refine ⟨38897055544144019983135631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25931370362762679988757087 38897055544144019983135631)
    ·
      refine ⟨58345583316216029974703447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38897055544144019983135631 58345583316216029974703447)
      ·
        refine ⟨87518374974324044962055171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58345583316216029974703447 87518374974324044962055171)
        ·
          refine ⟨131277562461486067443082757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87518374974324044962055171 131277562461486067443082757)
          ·
            refine ⟨24614542961528637645578017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131277562461486067443082757 24614542961528637645578017)
            ·
              refine ⟨18460907221146478234183513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24614542961528637645578017 18460907221146478234183513)
              ·
                refine ⟨13845680415859858675637635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18460907221146478234183513 13845680415859858675637635)
                ·
                  refine ⟨20768520623789788013456453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13845680415859858675637635 20768520623789788013456453)
                  ·
                    refine ⟨3894097616960585252523085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20768520623789788013456453 3894097616960585252523085)
                    ·
                      refine ⟨1460286606360219469696157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3894097616960585252523085 1460286606360219469696157)
                      ·
                        rfl

theorem cell23_2843898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_2843898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843898 prefixEnd_2843898 := by exact prefixLift 2843898
  have htrace : WordTrace (prefixWord ++ tailWord_2843898) baseStart_2843898 baseEnd_2843898 := by
    simpa [prefixWord, tailWord_2843898, baseEnd_2843898] using wordTrace_append hprefix tailTrace_2843898
  have hstable : (prefixWord ++ tailWord_2843898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843898).length < 2 ^ (prefixWord ++ tailWord_2843898).sum := by decide
  have hdescent : baseEnd_2843898 < baseStart_2843898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843901 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 12]
def baseStart_2843901 : Nat := 118140960795 + 2843901 * 2 ^ 59
def prefixEnd_2843901 : Nat := 4983230072969 + 3 ^ 40 * 2843901 * 2
def baseEnd_2843901 : Nat := 162254238533575884217627

theorem tailTrace_2843901 : CollatzResearch.WordTrace tailWord_2843901 prefixEnd_2843901 162254238533575884217627 := by
  unfold tailWord_2843901
  simp only [CollatzResearch.WordTrace]
  refine ⟨103725590870039851467387557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69150393913359900978258371 103725590870039851467387557)
  ·
    refine ⟨19448548288132472150135167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103725590870039851467387557 19448548288132472150135167)
    ·
      refine ⟨29172822432198708225202751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19448548288132472150135167 29172822432198708225202751)
      ·
        refine ⟨43759233648298062337804127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29172822432198708225202751 43759233648298062337804127)
        ·
          refine ⟨65638850472447093506706191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43759233648298062337804127 65638850472447093506706191)
          ·
            refine ⟨98458275708670640260059287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65638850472447093506706191 98458275708670640260059287)
            ·
              refine ⟨147687413563005960390088931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98458275708670640260059287 147687413563005960390088931)
              ·
                refine ⟨221531120344508940585133397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147687413563005960390088931 221531120344508940585133397)
                ·
                  refine ⟨162254238533575884217627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 221531120344508940585133397 162254238533575884217627)
                  ·
                    rfl

theorem cell23_2843901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_2843901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843901 prefixEnd_2843901 := by exact prefixLift 2843901
  have htrace : WordTrace (prefixWord ++ tailWord_2843901) baseStart_2843901 baseEnd_2843901 := by
    simpa [prefixWord, tailWord_2843901, baseEnd_2843901] using wordTrace_append hprefix tailTrace_2843901
  have hstable : (prefixWord ++ tailWord_2843901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843901).length < 2 ^ (prefixWord ++ tailWord_2843901).sum := by decide
  have hdescent : baseEnd_2843901 < baseStart_2843901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843905 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 3, 4]
def baseStart_2843905 : Nat := 118140960795 + 2843905 * 2 ^ 59
def prefixEnd_2843905 : Nat := 4983230072969 + 3 ^ 40 * 2843905 * 2
def baseEnd_2843905 : Nat := 486763400241600314102875

theorem tailTrace_2843905 : CollatzResearch.WordTrace tailWord_2843905 prefixEnd_2843905 486763400241600314102875 := by
  unfold tailWord_2843905
  simp only [CollatzResearch.WordTrace]
  refine ⟨103725736762025360150533169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69150491174683573433688779 103725736762025360150533169)
  ·
    refine ⟨77794302571519020112899877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103725736762025360150533169 77794302571519020112899877)
    ·
      refine ⟨14586431732159816271168727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77794302571519020112899877 14586431732159816271168727)
      ·
        refine ⟨21879647598239724406753091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14586431732159816271168727 21879647598239724406753091)
        ·
          refine ⟨32819471397359586610129637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21879647598239724406753091 32819471397359586610129637)
          ·
            refine ⟨6153650887004922489399307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32819471397359586610129637 6153650887004922489399307)
            ·
              refine ⟨9230476330507383734098961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6153650887004922489399307 9230476330507383734098961)
              ·
                refine ⟨6922857247880537800574221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9230476330507383734098961 6922857247880537800574221)
                ·
                  refine ⟨2596071467955201675215333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6922857247880537800574221 2596071467955201675215333)
                  ·
                    refine ⟨486763400241600314102875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2596071467955201675215333 486763400241600314102875)
                    ·
                      rfl

theorem cell23_2843905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_2843905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843905 prefixEnd_2843905 := by exact prefixLift 2843905
  have htrace : WordTrace (prefixWord ++ tailWord_2843905) baseStart_2843905 baseEnd_2843905 := by
    simpa [prefixWord, tailWord_2843905, baseEnd_2843905] using wordTrace_append hprefix tailTrace_2843905
  have hstable : (prefixWord ++ tailWord_2843905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843905).length < 2 ^ (prefixWord ++ tailWord_2843905).sum := by decide
  have hdescent : baseEnd_2843905 < baseStart_2843905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843912 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_2843912 : Nat := 118140960795 + 2843912 * 2 ^ 59
def prefixEnd_2843912 : Nat := 4983230072969 + 3 ^ 40 * 2843912 * 2
def baseEnd_2843912 : Nat := 1460293795089382414921093

theorem tailTrace_2843912 : CollatzResearch.WordTrace tailWord_2843912 prefixEnd_2843912 1460293795089382414921093 := by
  unfold tailWord_2843912
  simp only [CollatzResearch.WordTrace]
  refine ⟨51862996036500000173018995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69150661382000000230691993 51862996036500000173018995)
  ·
    refine ⟨77794494054750000259528493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51862996036500000173018995 77794494054750000259528493)
    ·
      refine ⟨29172935270531250097323185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77794494054750000259528493 29172935270531250097323185)
      ·
        refine ⟨21879701452898437572992389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29172935270531250097323185 21879701452898437572992389)
        ·
          refine ⟨4102444022418457044936073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21879701452898437572992389 4102444022418457044936073)
          ·
            refine ⟨3076833016813842783702055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4102444022418457044936073 3076833016813842783702055)
            ·
              refine ⟨4615249525220764175553083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3076833016813842783702055 4615249525220764175553083)
              ·
                refine ⟨6922874287831146263329625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4615249525220764175553083 6922874287831146263329625)
                ·
                  refine ⟨5192155715873359697497219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6922874287831146263329625 5192155715873359697497219)
                  ·
                    refine ⟨7788233573810039546245829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5192155715873359697497219 7788233573810039546245829)
                    ·
                      refine ⟨1460293795089382414921093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7788233573810039546245829 1460293795089382414921093)
                      ·
                        rfl

theorem cell23_2843912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_2843912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843912 prefixEnd_2843912 := by exact prefixLift 2843912
  have htrace : WordTrace (prefixWord ++ tailWord_2843912) baseStart_2843912 baseEnd_2843912 := by
    simpa [prefixWord, tailWord_2843912, baseEnd_2843912] using wordTrace_append hprefix tailTrace_2843912
  have hstable : (prefixWord ++ tailWord_2843912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843912).length < 2 ^ (prefixWord ++ tailWord_2843912).sum := by decide
  have hdescent : baseEnd_2843912 < baseStart_2843912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843915 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 3]
def baseStart_2843915 : Nat := 118140960795 + 2843915 * 2 ^ 59
def prefixEnd_2843915 : Nat := 4983230072969 + 3 ^ 40 * 2843915 * 2
def baseEnd_2843915 : Nat := 1460295335531345903183579

theorem tailTrace_2843915 : CollatzResearch.WordTrace tailWord_2843915 prefixEnd_2843915 1460295335531345903183579 := by
  unfold tailWord_2843915
  simp only [CollatzResearch.WordTrace]
  refine ⟨103726101491989131858397199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69150734327992754572264799 103726101491989131858397199)
  ·
    refine ⟨155589152237983697787595799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103726101491989131858397199 155589152237983697787595799)
    ·
      refine ⟨233383728356975546681393699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155589152237983697787595799 233383728356975546681393699)
      ·
        refine ⟨350075592535463320022090549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233383728356975546681393699 350075592535463320022090549)
        ·
          refine ⟨32819586800199686252070989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 350075592535463320022090549 32819586800199686252070989)
          ·
            refine ⟨12307345050074882344526621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32819586800199686252070989 12307345050074882344526621)
            ·
              refine ⟨4615254393778080879197483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12307345050074882344526621 4615254393778080879197483)
              ·
                refine ⟨6922881590667121318796225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4615254393778080879197483 6922881590667121318796225)
                ·
                  refine ⟨5192161193000340989097169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6922881590667121318796225 5192161193000340989097169)
                  ·
                    refine ⟨3894120894750255741822877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5192161193000340989097169 3894120894750255741822877)
                    ·
                      refine ⟨1460295335531345903183579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3894120894750255741822877 1460295335531345903183579)
                      ·
                        rfl

theorem cell23_2843915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 3].length) (baseStart_2843915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843915 prefixEnd_2843915 := by exact prefixLift 2843915
  have htrace : WordTrace (prefixWord ++ tailWord_2843915) baseStart_2843915 baseEnd_2843915 := by
    simpa [prefixWord, tailWord_2843915, baseEnd_2843915] using wordTrace_append hprefix tailTrace_2843915
  have hstable : (prefixWord ++ tailWord_2843915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843915).length < 2 ^ (prefixWord ++ tailWord_2843915).sum := by decide
  have hdescent : baseEnd_2843915 < baseStart_2843915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843955 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 1, 5, 2]
def baseStart_2843955 : Nat := 118140960795 + 2843955 * 2 ^ 59
def prefixEnd_2843955 : Nat := 4983230072969 + 3 ^ 40 * 2843955 * 2
def baseEnd_2843955 : Nat := 1460315874757525746683395

theorem tailTrace_2843955 : CollatzResearch.WordTrace tailWord_2843955 prefixEnd_2843955 1460315874757525746683395 := by
  unfold tailWord_2843955
  simp only [CollatzResearch.WordTrace]
  refine ⟨103727560411844218689853319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69151706941229479126568879 103727560411844218689853319)
  ·
    refine ⟨155591340617766328034779979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103727560411844218689853319 155591340617766328034779979)
    ·
      refine ⟨233387010926649492052169969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155591340617766328034779979 233387010926649492052169969)
      ·
        refine ⟨175040258194987119039127477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233387010926649492052169969 175040258194987119039127477)
        ·
          refine ⟨16410024205780042409918201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175040258194987119039127477 16410024205780042409918201)
          ·
            refine ⟨12307518154335031807438651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16410024205780042409918201 12307518154335031807438651)
            ·
              refine ⟨18461277231502547711157977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12307518154335031807438651 18461277231502547711157977)
              ·
                refine ⟨13845957923626910783368483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18461277231502547711157977 13845957923626910783368483)
                ·
                  refine ⟨20768936885440366175052725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13845957923626910783368483 20768936885440366175052725)
                  ·
                    refine ⟨1947087833010034328911193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20768936885440366175052725 1947087833010034328911193)
                    ·
                      refine ⟨1460315874757525746683395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1947087833010034328911193 1460315874757525746683395)
                      ·
                        rfl

theorem cell23_2843955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 5, 2].length) (baseStart_2843955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843955 prefixEnd_2843955 := by exact prefixLift 2843955
  have htrace : WordTrace (prefixWord ++ tailWord_2843955) baseStart_2843955 baseEnd_2843955 := by
    simpa [prefixWord, tailWord_2843955, baseEnd_2843955] using wordTrace_append hprefix tailTrace_2843955
  have hstable : (prefixWord ++ tailWord_2843955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843955).length < 2 ^ (prefixWord ++ tailWord_2843955).sum := by decide
  have hdescent : baseEnd_2843955 < baseStart_2843955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843978 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 1, 6]
def baseStart_2843978 : Nat := 118140960795 + 2843978 * 2 ^ 59
def prefixEnd_2843978 : Nat := 4983230072969 + 3 ^ 40 * 2843978 * 2
def baseEnd_2843978 : Nat := 486775894937526385565263

theorem tailTrace_2843978 : CollatzResearch.WordTrace tailWord_2843978 prefixEnd_2843978 486775894937526385565263 := by
  unfold tailWord_2843978
  simp only [CollatzResearch.WordTrace]
  refine ⟨25932099822690223404485147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69152266193840595745293725 25932099822690223404485147)
  ·
    refine ⟨38898149734035335106727721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25932099822690223404485147 38898149734035335106727721)
    ·
      refine ⟨29173612300526501330045791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38898149734035335106727721 29173612300526501330045791)
      ·
        refine ⟨43760418450789751995068687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29173612300526501330045791 43760418450789751995068687)
        ·
          refine ⟨65640627676184627992603031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43760418450789751995068687 65640627676184627992603031)
          ·
            refine ⟨98460941514276941988904547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65640627676184627992603031 98460941514276941988904547)
            ·
              refine ⟨147691412271415412983356821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98460941514276941988904547 147691412271415412983356821)
              ·
                refine ⟨6923034950222597483594851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147691412271415412983356821 6923034950222597483594851)
                ·
                  refine ⟨10384552425333896225392277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6923034950222597483594851 10384552425333896225392277)
                  ·
                    refine ⟨486775894937526385565263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10384552425333896225392277 486775894937526385565263)
                    ·
                      rfl

theorem cell23_2843978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_2843978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843978 prefixEnd_2843978 := by exact prefixLift 2843978
  have htrace : WordTrace (prefixWord ++ tailWord_2843978) baseStart_2843978 baseEnd_2843978 := by
    simpa [prefixWord, tailWord_2843978, baseEnd_2843978] using wordTrace_append hprefix tailTrace_2843978
  have hstable : (prefixWord ++ tailWord_2843978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843978).length < 2 ^ (prefixWord ++ tailWord_2843978).sum := by decide
  have hdescent : baseEnd_2843978 < baseStart_2843978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843985 : List Nat := [1, 2, 2, 1, 4, 1, 1, 5, 1, 1, 4]
def baseStart_2843985 : Nat := 118140960795 + 2843985 * 2 ^ 59
def prefixEnd_2843985 : Nat := 4983230072969 + 3 ^ 40 * 2843985 * 2
def baseEnd_2843985 : Nat := 1460331279177160629308257

theorem tailTrace_2843985 : CollatzResearch.WordTrace tailWord_2843985 prefixEnd_2843985 1460331279177160629308257 := by
  unfold tailWord_2843985
  simp only [CollatzResearch.WordTrace]
  refine ⟨103728654601735533813445409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69152436401157022542296939 103728654601735533813445409)
  ·
    refine ⟨77796490951301650360084057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103728654601735533813445409 77796490951301650360084057)
    ·
      refine ⟨58347368213476237770063043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77796490951301650360084057 58347368213476237770063043)
      ·
        refine ⟨87521052320214356655094565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58347368213476237770063043 87521052320214356655094565)
        ·
          refine ⟨16410197310040191872830231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87521052320214356655094565 16410197310040191872830231)
          ·
            refine ⟨24615295965060287809245347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16410197310040191872830231 24615295965060287809245347)
            ·
              refine ⟨36922943947590431713868021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24615295965060287809245347 36922943947590431713868021)
              ·
                refine ⟨3461525995086602973175127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36922943947590431713868021 3461525995086602973175127)
                ·
                  refine ⟨5192288992629904459762691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461525995086602973175127 5192288992629904459762691)
                  ·
                    refine ⟨7788433488944856689644037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5192288992629904459762691 7788433488944856689644037)
                    ·
                      refine ⟨1460331279177160629308257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7788433488944856689644037 1460331279177160629308257)
                      ·
                        rfl

theorem cell23_2843985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_2843985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843985 prefixEnd_2843985 := by exact prefixLift 2843985
  have htrace : WordTrace (prefixWord ++ tailWord_2843985) baseStart_2843985 baseEnd_2843985 := by
    simpa [prefixWord, tailWord_2843985, baseEnd_2843985] using wordTrace_append hprefix tailTrace_2843985
  have hstable : (prefixWord ++ tailWord_2843985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843985).length < 2 ^ (prefixWord ++ tailWord_2843985).sum := by decide
  have hdescent : baseEnd_2843985 < baseStart_2843985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2843990 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2843990 : Nat := 118140960795 + 2843990 * 2 ^ 59
def prefixEnd_2843990 : Nat := 4983230072969 + 3 ^ 40 * 2843990 * 2
def baseEnd_2843990 : Nat := 486777948860144369915245

theorem tailTrace_2843990 : CollatzResearch.WordTrace tailWord_2843990 prefixEnd_2843990 486777948860144369915245 := by
  unfold tailWord_2843990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6483052310419838729211089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69152557977811613111584949 6483052310419838729211089)
  ·
    refine ⟨4862289232814879046908317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6483052310419838729211089 4862289232814879046908317)
    ·
      refine ⟨1823358462305579642590619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4862289232814879046908317 1823358462305579642590619)
      ·
        refine ⟨2735037693458369463885929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1823358462305579642590619 2735037693458369463885929)
        ·
          refine ⟨2051278270093777097914447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2735037693458369463885929 2051278270093777097914447)
          ·
            refine ⟨3076917405140665646871671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2051278270093777097914447 3076917405140665646871671)
            ·
              refine ⟨4615376107710998470307507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3076917405140665646871671 4615376107710998470307507)
              ·
                refine ⟨6923064161566497705461261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4615376107710998470307507 6923064161566497705461261)
                ·
                  refine ⟨2596149060587436639547973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6923064161566497705461261 2596149060587436639547973)
                  ·
                    refine ⟨486777948860144369915245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2596149060587436639547973 486777948860144369915245)
                    ·
                      rfl

theorem cell23_2843990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2843990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2843990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2843990 prefixEnd_2843990 := by exact prefixLift 2843990
  have htrace : WordTrace (prefixWord ++ tailWord_2843990) baseStart_2843990 baseEnd_2843990 := by
    simpa [prefixWord, tailWord_2843990, baseEnd_2843990] using wordTrace_append hprefix tailTrace_2843990
  have hstable : (prefixWord ++ tailWord_2843990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2843990).length < 2 ^ (prefixWord ++ tailWord_2843990).sum := by decide
  have hdescent : baseEnd_2843990 < baseStart_2843990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2843990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844005 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 3, 2, 3]
def baseStart_2844005 : Nat := 118140960795 + 2844005 * 2 ^ 59
def prefixEnd_2844005 : Nat := 4983230072969 + 3 ^ 40 * 2844005 * 2
def baseEnd_2844005 : Nat := 1460341548790250551058165

theorem tailTrace_2844005 : CollatzResearch.WordTrace tailWord_2844005 prefixEnd_2844005 1460341548790250551058165 := by
  unfold tailWord_2844005
  simp only [CollatzResearch.WordTrace]
  refine ⟨103729384061663077229173469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69152922707775384819448979 103729384061663077229173469)
  ·
    refine ⟨38898519023123653960940051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103729384061663077229173469 38898519023123653960940051)
    ·
      refine ⟨58347778534685480941410077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38898519023123653960940051 58347778534685480941410077)
      ·
        refine ⟨21880416950507055353028779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58347778534685480941410077 21880416950507055353028779)
        ·
          refine ⟨32820625425760583029543169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21880416950507055353028779 32820625425760583029543169)
          ·
            refine ⟨24615469069320437272157377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32820625425760583029543169 24615469069320437272157377)
            ·
              refine ⟨18461601801990327954118033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24615469069320437272157377 18461601801990327954118033)
              ·
                refine ⟨13846201351492745965588525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18461601801990327954118033 13846201351492745965588525)
                ·
                  refine ⟨5192325506809779737095697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13846201351492745965588525 5192325506809779737095697)
                  ·
                    refine ⟨3894244130107334802821773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5192325506809779737095697 3894244130107334802821773)
                    ·
                      refine ⟨1460341548790250551058165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3894244130107334802821773 1460341548790250551058165)
                      ·
                        rfl

theorem cell23_2844005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_2844005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844005 prefixEnd_2844005 := by exact prefixLift 2844005
  have htrace : WordTrace (prefixWord ++ tailWord_2844005) baseStart_2844005 baseEnd_2844005 := by
    simpa [prefixWord, tailWord_2844005, baseEnd_2844005] using wordTrace_append hprefix tailTrace_2844005
  have hstable : (prefixWord ++ tailWord_2844005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844005).length < 2 ^ (prefixWord ++ tailWord_2844005).sum := by decide
  have hdescent : baseEnd_2844005 < baseStart_2844005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844012 : List Nat := [2, 2, 1, 1, 5, 2, 1, 3, 2, 4]
def baseStart_2844012 : Nat := 118140960795 + 2844012 * 2 ^ 59
def prefixEnd_2844012 : Nat := 4983230072969 + 3 ^ 40 * 2844012 * 2
def baseEnd_2844012 : Nat := 486781714384944007890211

theorem tailTrace_2844012 : CollatzResearch.WordTrace tailWord_2844012 prefixEnd_2844012 486781714384944007890211 := by
  unfold tailWord_2844012
  simp only [CollatzResearch.WordTrace]
  refine ⟨51864819686318858712339145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69153092915091811616452193 51864819686318858712339145)
  ·
    refine ⟨38898614764739144034254359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51864819686318858712339145 38898614764739144034254359)
    ·
      refine ⟨58347922147108716051381539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38898614764739144034254359 58347922147108716051381539)
      ·
        refine ⟨87521883220663074077072309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58347922147108716051381539 87521883220663074077072309)
        ·
          refine ⟨8205176551937163194725529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87521883220663074077072309 8205176551937163194725529)
          ·
            refine ⟨6153882413952872396044147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8205176551937163194725529 6153882413952872396044147)
            ·
              refine ⟨9230823620929308594066221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6153882413952872396044147 9230823620929308594066221)
              ·
                refine ⟨3461558857848490722774833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9230823620929308594066221 3461558857848490722774833)
                ·
                  refine ⟨2596169143386368042081125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3461558857848490722774833 2596169143386368042081125)
                  ·
                    refine ⟨486781714384944007890211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2596169143386368042081125 486781714384944007890211)
                    ·
                      rfl

theorem cell23_2844012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_2844012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844012 prefixEnd_2844012 := by exact prefixLift 2844012
  have htrace : WordTrace (prefixWord ++ tailWord_2844012) baseStart_2844012 baseEnd_2844012 := by
    simpa [prefixWord, tailWord_2844012, baseEnd_2844012] using wordTrace_append hprefix tailTrace_2844012
  have hstable : (prefixWord ++ tailWord_2844012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844012).length < 2 ^ (prefixWord ++ tailWord_2844012).sum := by decide
  have hdescent : baseEnd_2844012 < baseStart_2844012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844035 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 3]
def baseStart_2844035 : Nat := 118140960795 + 2844035 * 2 ^ 59
def prefixEnd_2844035 : Nat := 4983230072969 + 3 ^ 40 * 2844035 * 2
def baseEnd_2844035 : Nat := 1460356953209885433683027

theorem tailTrace_2844035 : CollatzResearch.WordTrace tailWord_2844035 prefixEnd_2844035 1460356953209885433683027 := by
  unfold tailWord_2844035
  simp only [CollatzResearch.WordTrace]
  refine ⟨103730478251554392352765559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69153652167702928235177039 103730478251554392352765559)
  ·
    refine ⟨155595717377331588529148339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103730478251554392352765559 155595717377331588529148339)
    ·
      refine ⟨233393576065997382793722509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155595717377331588529148339 233393576065997382793722509)
      ·
        refine ⟨87522591024749018547645941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233393576065997382793722509 87522591024749018547645941)
        ·
          refine ⟨8205242908570220488841807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87522591024749018547645941 8205242908570220488841807)
          ·
            refine ⟨12307864362855330733262711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8205242908570220488841807 12307864362855330733262711)
            ·
              refine ⟨18461796544282996099894067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12307864362855330733262711 18461796544282996099894067)
              ·
                refine ⟨27692694816424494149841101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18461796544282996099894067 27692694816424494149841101)
                ·
                  refine ⟨10384760556159185306190413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27692694816424494149841101 10384760556159185306190413)
                  ·
                    refine ⟨3894285208559694489821405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10384760556159185306190413 3894285208559694489821405)
                    ·
                      refine ⟨1460356953209885433683027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3894285208559694489821405 1460356953209885433683027)
                      ·
                        rfl

theorem cell23_2844035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_2844035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844035 prefixEnd_2844035 := by exact prefixLift 2844035
  have htrace : WordTrace (prefixWord ++ tailWord_2844035) baseStart_2844035 baseEnd_2844035 := by
    simpa [prefixWord, tailWord_2844035, baseEnd_2844035] using wordTrace_append hprefix tailTrace_2844035
  have hstable : (prefixWord ++ tailWord_2844035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844035).length < 2 ^ (prefixWord ++ tailWord_2844035).sum := by decide
  have hdescent : baseEnd_2844035 < baseStart_2844035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844039 : List Nat := [1, 1, 4, 2, 2, 3, 3, 1, 1, 2, 3]
def baseStart_2844039 : Nat := 118140960795 + 2844039 * 2 ^ 59
def prefixEnd_2844039 : Nat := 4983230072969 + 3 ^ 40 * 2844039 * 2
def baseEnd_2844039 : Nat := 1460359007132503418033009

theorem tailTrace_2844039 : CollatzResearch.WordTrace tailWord_2844039 prefixEnd_2844039 1460359007132503418033009 := by
  unfold tailWord_2844039
  simp only [CollatzResearch.WordTrace]
  refine ⟨103730624143539901035911171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69153749429026600690607447 103730624143539901035911171)
  ·
    refine ⟨155595936215309851553866757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103730624143539901035911171 155595936215309851553866757)
    ·
      refine ⟨29174238040370597166350017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155595936215309851553866757 29174238040370597166350017)
      ·
        refine ⟨21880678530277947874762513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29174238040370597166350017 21880678530277947874762513)
        ·
          refine ⟨16410508897708460906071885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21880678530277947874762513 16410508897708460906071885)
          ·
            refine ⟨6153940836640672839776957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16410508897708460906071885 6153940836640672839776957)
            ·
              refine ⟨2307727813740252314916359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6153940836640672839776957 2307727813740252314916359)
              ·
                refine ⟨3461591720610378472374539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2307727813740252314916359 3461591720610378472374539)
                ·
                  refine ⟨5192387580915567708561809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461591720610378472374539 5192387580915567708561809)
                  ·
                    refine ⟨3894290685686675781421357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5192387580915567708561809 3894290685686675781421357)
                    ·
                      refine ⟨1460359007132503418033009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3894290685686675781421357 1460359007132503418033009)
                      ·
                        rfl

theorem cell23_2844039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_2844039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844039 prefixEnd_2844039 := by exact prefixLift 2844039
  have htrace : WordTrace (prefixWord ++ tailWord_2844039) baseStart_2844039 baseEnd_2844039 := by
    simpa [prefixWord, tailWord_2844039, baseEnd_2844039] using wordTrace_append hprefix tailTrace_2844039
  have hstable : (prefixWord ++ tailWord_2844039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844039).length < 2 ^ (prefixWord ++ tailWord_2844039).sum := by decide
  have hdescent : baseEnd_2844039 < baseStart_2844039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844145 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 1, 7]
def baseStart_2844145 : Nat := 118140960795 + 2844145 * 2 ^ 59
def prefixEnd_2844145 : Nat := 4983230072969 + 3 ^ 40 * 2844145 * 2
def baseEnd_2844145 : Nat := 486804478693960001102507

theorem tailTrace_2844145 : CollatzResearch.WordTrace tailWord_2844145 prefixEnd_2844145 486804478693960001102507 := by
  unfold tailWord_2844145
  simp only [CollatzResearch.WordTrace]
  refine ⟨103734490281155881139269889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69156326854103920759513259 103734490281155881139269889)
  ·
    refine ⟨77800867710866910854452417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103734490281155881139269889 77800867710866910854452417)
    ·
      refine ⟨58350650783150183140839313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77800867710866910854452417 58350650783150183140839313)
      ·
        refine ⟨43762988087362637355629485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58350650783150183140839313 43762988087362637355629485)
        ·
          refine ⟨16411120532760989008361057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43762988087362637355629485 16411120532760989008361057)
          ·
            refine ⟨12308340399570741756270793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16411120532760989008361057 12308340399570741756270793)
            ·
              refine ⟨9231255299678056317203095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12308340399570741756270793 9231255299678056317203095)
              ·
                refine ⟨13846882949517084475804643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9231255299678056317203095 13846882949517084475804643)
                ·
                  refine ⟨20770324424275626713706965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13846882949517084475804643 20770324424275626713706965)
                  ·
                    refine ⟨486804478693960001102507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20770324424275626713706965 486804478693960001102507)
                    ·
                      rfl

theorem cell23_2844145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_2844145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844145 prefixEnd_2844145 := by exact prefixLift 2844145
  have htrace : WordTrace (prefixWord ++ tailWord_2844145) baseStart_2844145 baseEnd_2844145 := by
    simpa [prefixWord, tailWord_2844145, baseEnd_2844145] using wordTrace_append hprefix tailTrace_2844145
  have hstable : (prefixWord ++ tailWord_2844145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844145).length < 2 ^ (prefixWord ++ tailWord_2844145).sum := by decide
  have hdescent : baseEnd_2844145 < baseStart_2844145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844172 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 1, 2, 5]
def baseStart_2844172 : Nat := 118140960795 + 2844172 * 2 ^ 59
def prefixEnd_2844172 : Nat := 4983230072969 + 3 ^ 40 * 2844172 * 2
def baseEnd_2844172 : Nat := 1460427300059551397669897

theorem tailTrace_2844172 : CollatzResearch.WordTrace tailWord_2844172 prefixEnd_2844172 1460427300059551397669897 := by
  unfold tailWord_2844172
  simp only [CollatzResearch.WordTrace]
  refine ⟨51867737526029032375251385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69156983368038709833668513 51867737526029032375251385)
  ·
    refine ⟨38900803144521774281438539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51867737526029032375251385 38900803144521774281438539)
    ·
      refine ⟨58351204716782661422157809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38900803144521774281438539 58351204716782661422157809)
      ·
        refine ⟨43763403537586996066618357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58351204716782661422157809 43763403537586996066618357)
        ·
          refine ⟨4102819081648780881245471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43763403537586996066618357 4102819081648780881245471)
          ·
            refine ⟨6154228622473171321868207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4102819081648780881245471 6154228622473171321868207)
            ·
              refine ⟨9231342933709756982802311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6154228622473171321868207 9231342933709756982802311)
              ·
                refine ⟨13847014400564635474203467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9231342933709756982802311 13847014400564635474203467)
                ·
                  refine ⟨20770521600846953211305201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13847014400564635474203467 20770521600846953211305201)
                  ·
                    refine ⟨15577891200635214908478901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20770521600846953211305201 15577891200635214908478901)
                    ·
                      refine ⟨1460427300059551397669897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15577891200635214908478901 1460427300059551397669897)
                      ·
                        rfl

theorem cell23_2844172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_2844172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844172 prefixEnd_2844172 := by exact prefixLift 2844172
  have htrace : WordTrace (prefixWord ++ tailWord_2844172) baseStart_2844172 baseEnd_2844172 := by
    simpa [prefixWord, tailWord_2844172, baseEnd_2844172] using wordTrace_append hprefix tailTrace_2844172
  have hstable : (prefixWord ++ tailWord_2844172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844172).length < 2 ^ (prefixWord ++ tailWord_2844172).sum := by decide
  have hdescent : baseEnd_2844172 < baseStart_2844172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844209 : List Nat := [1, 2, 2, 3, 1, 1, 1, 7, 1, 4]
def baseStart_2844209 : Nat := 118140960795 + 2844209 * 2 ^ 59
def prefixEnd_2844209 : Nat := 4983230072969 + 3 ^ 40 * 2844209 * 2
def baseEnd_2844209 : Nat := 486815432947922584302409

theorem tailTrace_2844209 : CollatzResearch.WordTrace tailWord_2844209 prefixEnd_2844209 486815432947922584302409 := by
  unfold tailWord_2844209
  simp only [CollatzResearch.WordTrace]
  refine ⟨103736824552924020069599681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69157883035282680046399787 103736824552924020069599681)
  ·
    refine ⟨77802618414693015052199761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103736824552924020069599681 77802618414693015052199761)
    ·
      refine ⟨58351963811019761289149821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77802618414693015052199761 58351963811019761289149821)
      ·
        refine ⟨21881986429132410483431183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58351963811019761289149821 21881986429132410483431183)
        ·
          refine ⟨32822979643698615725146775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21881986429132410483431183 32822979643698615725146775)
          ·
            refine ⟨49234469465547923587720163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32822979643698615725146775 49234469465547923587720163)
            ·
              refine ⟨73851704198321885381580245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49234469465547923587720163 73851704198321885381580245)
              ·
                refine ⟨1730899317148169188630787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73851704198321885381580245 1730899317148169188630787)
                ·
                  refine ⟨2596348975722253782946181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1730899317148169188630787 2596348975722253782946181)
                  ·
                    refine ⟨486815432947922584302409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2596348975722253782946181 486815432947922584302409)
                    ·
                      rfl

theorem cell23_2844209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_2844209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844209 prefixEnd_2844209 := by exact prefixLift 2844209
  have htrace : WordTrace (prefixWord ++ tailWord_2844209) baseStart_2844209 baseEnd_2844209 := by
    simpa [prefixWord, tailWord_2844209, baseEnd_2844209] using wordTrace_append hprefix tailTrace_2844209
  have hstable : (prefixWord ++ tailWord_2844209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844209).length < 2 ^ (prefixWord ++ tailWord_2844209).sum := by decide
  have hdescent : baseEnd_2844209 < baseStart_2844209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844245 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2844245 : Nat := 118140960795 + 2844245 * 2 ^ 59
def prefixEnd_2844245 : Nat := 4983230072969 + 3 ^ 40 * 2844245 * 2
def baseEnd_2844245 : Nat := 1460464784147329612057061

theorem tailTrace_2844245 : CollatzResearch.WordTrace tailWord_2844245 prefixEnd_2844245 1460464784147329612057061 := by
  unfold tailWord_2844245
  simp only [CollatzResearch.WordTrace]
  refine ⟨103738137580793598217910189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69158758387195732145273459 103738137580793598217910189)
  ·
    refine ⟨38901801592797599331716321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103738137580793598217910189 38901801592797599331716321)
    ·
      refine ⟨29176351194598199498787241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38901801592797599331716321 29176351194598199498787241)
      ·
        refine ⟨21882263395948649624090431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29176351194598199498787241 21882263395948649624090431)
        ·
          refine ⟨32823395093922974436135647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21882263395948649624090431 32823395093922974436135647)
          ·
            refine ⟨49235092640884461654203471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32823395093922974436135647 49235092640884461654203471)
            ·
              refine ⟨73852638961326692481305207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49235092640884461654203471 73852638961326692481305207)
              ·
                refine ⟨110778958441990038721957811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73852638961326692481305207 110778958441990038721957811)
                ·
                  refine ⟨166168437662985058082936717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110778958441990038721957811 166168437662985058082936717)
                  ·
                    refine ⟨62313164123619396781101269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166168437662985058082936717 62313164123619396781101269)
                    ·
                      refine ⟨1460464784147329612057061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62313164123619396781101269 1460464784147329612057061)
                      ·
                        rfl

theorem cell23_2844245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2844245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844245 prefixEnd_2844245 := by exact prefixLift 2844245
  have htrace : WordTrace (prefixWord ++ tailWord_2844245) baseStart_2844245 baseEnd_2844245 := by
    simpa [prefixWord, tailWord_2844245, baseEnd_2844245] using wordTrace_append hprefix tailTrace_2844245
  have hstable : (prefixWord ++ tailWord_2844245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844245).length < 2 ^ (prefixWord ++ tailWord_2844245).sum := by decide
  have hdescent : baseEnd_2844245 < baseStart_2844245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844259 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 1, 5, 2]
def baseStart_2844259 : Nat := 118140960795 + 2844259 * 2 ^ 59
def prefixEnd_2844259 : Nat := 4983230072969 + 3 ^ 40 * 2844259 * 2
def baseEnd_2844259 : Nat := 1460471972876492557281997

theorem tailTrace_2844259 : CollatzResearch.WordTrace tailWord_2844259 prefixEnd_2844259 1460471972876492557281997 := by
  unfold tailWord_2844259
  simp only [CollatzResearch.WordTrace]
  refine ⟨103738648202742878608919831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69159098801828585739279887 103738648202742878608919831)
  ·
    refine ⟨155607972304114317913379747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103738648202742878608919831 155607972304114317913379747)
    ·
      refine ⟨233411958456171476870069621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155607972304114317913379747 233411958456171476870069621)
      ·
        refine ⟨21882371105266075956569027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 233411958456171476870069621 21882371105266075956569027)
        ·
          refine ⟨32823556657899113934853541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21882371105266075956569027 32823556657899113934853541)
          ·
            refine ⟨6154416873356083862785039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32823556657899113934853541 6154416873356083862785039)
            ·
              refine ⟨9231625310034125794177559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6154416873356083862785039 9231625310034125794177559)
              ·
                refine ⟨13847437965051188691266339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9231625310034125794177559 13847437965051188691266339)
                ·
                  refine ⟨20771156947576783036899509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13847437965051188691266339 20771156947576783036899509)
                  ·
                    refine ⟨1947295963835323409709329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20771156947576783036899509 1947295963835323409709329)
                    ·
                      refine ⟨1460471972876492557281997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1947295963835323409709329 1460471972876492557281997)
                      ·
                        rfl

theorem cell23_2844259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_2844259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844259 prefixEnd_2844259 := by exact prefixLift 2844259
  have htrace : WordTrace (prefixWord ++ tailWord_2844259) baseStart_2844259 baseEnd_2844259 := by
    simpa [prefixWord, tailWord_2844259, baseEnd_2844259] using wordTrace_append hprefix tailTrace_2844259
  have hstable : (prefixWord ++ tailWord_2844259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844259).length < 2 ^ (prefixWord ++ tailWord_2844259).sum := by decide
  have hdescent : baseEnd_2844259 < baseStart_2844259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844312 : List Nat := [2, 1, 2, 4, 1, 3, 1, 9]
def baseStart_2844312 : Nat := 118140960795 + 2844312 * 2 ^ 59
def prefixEnd_2844312 : Nat := 4983230072969 + 3 ^ 40 * 2844312 * 2
def baseEnd_2844312 : Nat := 54092562494488179626639

theorem tailTrace_2844312 : CollatzResearch.WordTrace tailWord_2844312 prefixEnd_2844312 54092562494488179626639 := by
  unfold tailWord_2844312
  simp only [CollatzResearch.WordTrace]
  refine ⟨51870290635775434330299595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69160387514367245773732793 51870290635775434330299595)
  ·
    refine ⟨77805435953663151495449393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51870290635775434330299595 77805435953663151495449393)
    ·
      refine ⟨58354076965247363621587045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77805435953663151495449393 58354076965247363621587045)
      ·
        refine ⟨10941389430983880679047571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58354076965247363621587045 10941389430983880679047571)
        ·
          refine ⟨16412084146475821018571357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10941389430983880679047571 16412084146475821018571357)
          ·
            refine ⟨6154531554928432881964259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16412084146475821018571357 6154531554928432881964259)
            ·
              refine ⟨9231797332392649322946389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6154531554928432881964259 9231797332392649322946389)
              ·
                refine ⟨54092562494488179626639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9231797332392649322946389 54092562494488179626639)
                ·
                  rfl

theorem cell23_2844312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 9].length) (baseStart_2844312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844312 prefixEnd_2844312 := by exact prefixLift 2844312
  have htrace : WordTrace (prefixWord ++ tailWord_2844312) baseStart_2844312 baseEnd_2844312 := by
    simpa [prefixWord, tailWord_2844312, baseEnd_2844312] using wordTrace_append hprefix tailTrace_2844312
  have hstable : (prefixWord ++ tailWord_2844312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844312).length < 2 ^ (prefixWord ++ tailWord_2844312).sum := by decide
  have hdescent : baseEnd_2844312 < baseStart_2844312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844339 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 4, 1, 3]
def baseStart_2844339 : Nat := 118140960795 + 2844339 * 2 ^ 59
def prefixEnd_2844339 : Nat := 4983230072969 + 3 ^ 40 * 2844339 * 2
def baseEnd_2844339 : Nat := 1460513051328852244281629

theorem tailTrace_2844339 : CollatzResearch.WordTrace tailWord_2844339 prefixEnd_2844339 1460513051328852244281629 := by
  unfold tailWord_2844339
  simp only [CollatzResearch.WordTrace]
  refine ⟨103741566042453052271832071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69161044028302034847888047 103741566042453052271832071)
  ·
    refine ⟨155612349063679578407748107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103741566042453052271832071 155612349063679578407748107)
    ·
      refine ⟨233418523595519367611622161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155612349063679578407748107 233418523595519367611622161)
      ·
        refine ⟨175063892696639525708716621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233418523595519367611622161 175063892696639525708716621)
        ·
          refine ⟨65648959761239822140768733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175063892696639525708716621 65648959761239822140768733)
          ·
            refine ⟨24618359910464933302788275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65648959761239822140768733 24618359910464933302788275)
            ·
              refine ⟨36927539865697399954182413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24618359910464933302788275 36927539865697399954182413)
              ·
                refine ⟨13847827449636524982818405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36927539865697399954182413 13847827449636524982818405)
                ·
                  refine ⟨2596467646806848434278451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13847827449636524982818405 2596467646806848434278451)
                  ·
                    refine ⟨3894701470210272651417677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2596467646806848434278451 3894701470210272651417677)
                    ·
                      refine ⟨1460513051328852244281629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3894701470210272651417677 1460513051328852244281629)
                      ·
                        rfl

theorem cell23_2844339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 1, 3].length) (baseStart_2844339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844339 prefixEnd_2844339 := by exact prefixLift 2844339
  have htrace : WordTrace (prefixWord ++ tailWord_2844339) baseStart_2844339 baseEnd_2844339 := by
    simpa [prefixWord, tailWord_2844339, baseEnd_2844339] using wordTrace_append hprefix tailTrace_2844339
  have hstable : (prefixWord ++ tailWord_2844339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844339).length < 2 ^ (prefixWord ++ tailWord_2844339).sum := by decide
  have hdescent : baseEnd_2844339 < baseStart_2844339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844366 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2]
def baseStart_2844366 : Nat := 118140960795 + 2844366 * 2 ^ 59
def prefixEnd_2844366 : Nat := 4983230072969 + 3 ^ 40 * 2844366 * 2
def baseEnd_2844366 : Nat := 1460526915306523638644005

theorem tailTrace_2844366 : CollatzResearch.WordTrace tailWord_2844366 prefixEnd_2844366 1460526915306523638644005 := by
  unfold tailWord_2844366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12967818851669404485383119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69161700542236823922043301 12967818851669404485383119)
  ·
    refine ⟨19451728277504106728074679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12967818851669404485383119 19451728277504106728074679)
    ·
      refine ⟨29177592416256160092112019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19451728277504106728074679 29177592416256160092112019)
      ·
        refine ⟨43766388624384240138168029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29177592416256160092112019 43766388624384240138168029)
        ·
          refine ⟨16412395734144090051813011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43766388624384240138168029 16412395734144090051813011)
          ·
            refine ⟨24618593601216135077719517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16412395734144090051813011 24618593601216135077719517)
            ·
              refine ⟨9231972600456050654144819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24618593601216135077719517 9231972600456050654144819)
              ·
                refine ⟨13847958900684075981217229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9231972600456050654144819 13847958900684075981217229)
                ·
                  refine ⟨5192984587756528492956461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13847958900684075981217229 5192984587756528492956461)
                  ·
                    refine ⟨1947369220408698184858673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5192984587756528492956461 1947369220408698184858673)
                    ·
                      refine ⟨1460526915306523638644005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1947369220408698184858673 1460526915306523638644005)
                      ·
                        rfl

theorem cell23_2844366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_2844366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844366 prefixEnd_2844366 := by exact prefixLift 2844366
  have htrace : WordTrace (prefixWord ++ tailWord_2844366) baseStart_2844366 baseEnd_2844366 := by
    simpa [prefixWord, tailWord_2844366, baseEnd_2844366] using wordTrace_append hprefix tailTrace_2844366
  have hstable : (prefixWord ++ tailWord_2844366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844366).length < 2 ^ (prefixWord ++ tailWord_2844366).sum := by decide
  have hdescent : baseEnd_2844366 < baseStart_2844366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844383 : List Nat := [1, 1, 2, 3, 2, 2, 5, 1, 1, 3, 2]
def baseStart_2844383 : Nat := 118140960795 + 2844383 * 2 ^ 59
def prefixEnd_2844383 : Nat := 4983230072969 + 3 ^ 40 * 2844383 * 2
def baseEnd_2844383 : Nat := 1460535644477650072131427

theorem tailTrace_2844383 : CollatzResearch.WordTrace tailWord_2844383 prefixEnd_2844383 1460535644477650072131427 := by
  unfold tailWord_2844383
  simp only [CollatzResearch.WordTrace]
  refine ⟨103743170854293647786433803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69162113902862431857622535 103743170854293647786433803)
  ·
    refine ⟨155614756281440471679650705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103743170854293647786433803 155614756281440471679650705)
    ·
      refine ⟨116711067211080353759738029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155614756281440471679650705 116711067211080353759738029)
      ·
        refine ⟨43766650204155132659901761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116711067211080353759738029 43766650204155132659901761)
        ·
          refine ⟨32824987653116349494926321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43766650204155132659901761 32824987653116349494926321)
          ·
            refine ⟨24618740739837262121194741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32824987653116349494926321 24618740739837262121194741)
            ·
              refine ⟨2308006944359743323862007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24618740739837262121194741 2308006944359743323862007)
              ·
                refine ⟨3462010416539614985793011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2308006944359743323862007 3462010416539614985793011)
                ·
                  refine ⟨5193015624809422478689517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3462010416539614985793011 5193015624809422478689517)
                  ·
                    refine ⟨1947380859303533429508569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5193015624809422478689517 1947380859303533429508569)
                    ·
                      refine ⟨1460535644477650072131427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1947380859303533429508569 1460535644477650072131427)
                      ·
                        rfl

theorem cell23_2844383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_2844383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844383 prefixEnd_2844383 := by exact prefixLift 2844383
  have htrace : WordTrace (prefixWord ++ tailWord_2844383) baseStart_2844383 baseEnd_2844383 := by
    simpa [prefixWord, tailWord_2844383, baseEnd_2844383] using wordTrace_append hprefix tailTrace_2844383
  have hstable : (prefixWord ++ tailWord_2844383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844383).length < 2 ^ (prefixWord ++ tailWord_2844383).sum := by decide
  have hdescent : baseEnd_2844383 < baseStart_2844383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844391 : List Nat := [1, 1, 5, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2844391 : Nat := 118140960795 + 2844391 * 2 ^ 59
def prefixEnd_2844391 : Nat := 4983230072969 + 3 ^ 40 * 2844391 * 2
def baseEnd_2844391 : Nat := 1460539752322886040831391

theorem tailTrace_2844391 : CollatzResearch.WordTrace tailWord_2844391 prefixEnd_2844391 1460539752322886040831391 := by
  unfold tailWord_2844391
  simp only [CollatzResearch.WordTrace]
  refine ⟨103743462638264665152725027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69162308425509776768483351 103743462638264665152725027)
  ·
    refine ⟨155615193957396997729087541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103743462638264665152725027 155615193957396997729087541)
    ·
      refine ⟨14588924433505968537101957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155615193957396997729087541 14588924433505968537101957)
      ·
        refine ⟨2735423331282369100706617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14588924433505968537101957 2735423331282369100706617)
        ·
          refine ⟨2051567498461776825529963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2735423331282369100706617 2051567498461776825529963)
          ·
            refine ⟨3077351247692665238294945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2051567498461776825529963 3077351247692665238294945)
            ·
              refine ⟨2308013435769498928721209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3077351247692665238294945 2308013435769498928721209)
              ·
                refine ⟨1731010076827124196540907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2308013435769498928721209 1731010076827124196540907)
                ·
                  refine ⟨2596515115240686294811361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1731010076827124196540907 2596515115240686294811361)
                  ·
                    refine ⟨1947386336430514721108521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2596515115240686294811361 1947386336430514721108521)
                    ·
                      refine ⟨1460539752322886040831391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1947386336430514721108521 1460539752322886040831391)
                      ·
                        rfl

theorem cell23_2844391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2844391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844391 prefixEnd_2844391 := by exact prefixLift 2844391
  have htrace : WordTrace (prefixWord ++ tailWord_2844391) baseStart_2844391 baseEnd_2844391 := by
    simpa [prefixWord, tailWord_2844391, baseEnd_2844391] using wordTrace_append hprefix tailTrace_2844391
  have hstable : (prefixWord ++ tailWord_2844391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844391).length < 2 ^ (prefixWord ++ tailWord_2844391).sum := by decide
  have hdescent : baseEnd_2844391 < baseStart_2844391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844396 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 4, 2, 2]
def baseStart_2844396 : Nat := 118140960795 + 2844396 * 2 ^ 59
def prefixEnd_2844396 : Nat := 4983230072969 + 3 ^ 40 * 2844396 * 2
def baseEnd_2844396 : Nat := 1460542319726158521268867

theorem tailTrace_2844396 : CollatzResearch.WordTrace tailWord_2844396 prefixEnd_2844396 1460542319726158521268867 := by
  unfold tailWord_2844396
  simp only [CollatzResearch.WordTrace]
  refine ⟨51871822501623275503328521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69162430002164367337771361 51871822501623275503328521)
  ·
    refine ⟨38903866876217456627496391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51871822501623275503328521 38903866876217456627496391)
    ·
      refine ⟨58355800314326184941244587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38903866876217456627496391 58355800314326184941244587)
      ·
        refine ⟨87533700471489277411866881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58355800314326184941244587 87533700471489277411866881)
        ·
          refine ⟨65650275353616958058900161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87533700471489277411866881 65650275353616958058900161)
          ·
            refine ⟨49237706515212718544175121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65650275353616958058900161 49237706515212718544175121)
            ·
              refine ⟨36928279886409538908131341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49237706515212718544175121 36928279886409538908131341)
              ·
                refine ⟨13848104957403577090549253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36928279886409538908131341 13848104957403577090549253)
                ·
                  refine ⟨2596519679513170704477985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13848104957403577090549253 2596519679513170704477985)
                  ·
                    refine ⟨1947389759634878028358489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2596519679513170704477985 1947389759634878028358489)
                    ·
                      refine ⟨1460542319726158521268867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1947389759634878028358489 1460542319726158521268867)
                      ·
                        rfl

theorem cell23_2844396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 2, 2].length) (baseStart_2844396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844396 prefixEnd_2844396 := by exact prefixLift 2844396
  have htrace : WordTrace (prefixWord ++ tailWord_2844396) baseStart_2844396 baseEnd_2844396 := by
    simpa [prefixWord, tailWord_2844396, baseEnd_2844396] using wordTrace_append hprefix tailTrace_2844396
  have hstable : (prefixWord ++ tailWord_2844396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844396).length < 2 ^ (prefixWord ++ tailWord_2844396).sum := by decide
  have hdescent : baseEnd_2844396 < baseStart_2844396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844489 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 1, 4, 3]
def baseStart_2844489 : Nat := 118140960795 + 2844489 * 2 ^ 59
def prefixEnd_2844489 : Nat := 4983230072969 + 3 ^ 40 * 2844489 * 2
def baseEnd_2844489 : Nat := 1460590073427026657405939

theorem tailTrace_2844489 : CollatzResearch.WordTrace tailWord_2844489 prefixEnd_2844489 1460590073427026657405939 := by
  unfold tailWord_2844489
  simp only [CollatzResearch.WordTrace]
  refine ⟨103747036991909627889792521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69164691327939751926528347 103747036991909627889792521)
  ·
    refine ⟨77810277743932220917344391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103747036991909627889792521 77810277743932220917344391)
    ·
      refine ⟨116715416615898331376016587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77810277743932220917344391 116715416615898331376016587)
      ·
        refine ⟨175073124923847497064024881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116715416615898331376016587 175073124923847497064024881)
        ·
          refine ⟨131304843692885622798018661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175073124923847497064024881 131304843692885622798018661)
          ·
            refine ⟨24619658192416054274628499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131304843692885622798018661 24619658192416054274628499)
            ·
              refine ⟨36929487288624081411942749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24619658192416054274628499 36929487288624081411942749)
              ·
                refine ⟨13848557733234030529478531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36929487288624081411942749 13848557733234030529478531)
                ·
                  refine ⟨20772836599851045794217797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13848557733234030529478531 20772836599851045794217797)
                  ·
                    refine ⟨3894906862472071086415837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20772836599851045794217797 3894906862472071086415837)
                    ·
                      refine ⟨1460590073427026657405939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3894906862472071086415837 1460590073427026657405939)
                      ·
                        rfl

theorem cell23_2844489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 4, 3].length) (baseStart_2844489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844489 prefixEnd_2844489 := by exact prefixLift 2844489
  have htrace : WordTrace (prefixWord ++ tailWord_2844489) baseStart_2844489 baseEnd_2844489 := by
    simpa [prefixWord, tailWord_2844489, baseEnd_2844489] using wordTrace_append hprefix tailTrace_2844489
  have hstable : (prefixWord ++ tailWord_2844489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844489).length < 2 ^ (prefixWord ++ tailWord_2844489).sum := by decide
  have hdescent : baseEnd_2844489 < baseStart_2844489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844506 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3]
def baseStart_2844506 : Nat := 118140960795 + 2844506 * 2 ^ 59
def prefixEnd_2844506 : Nat := 4983230072969 + 3 ^ 40 * 2844506 * 2
def baseEnd_2844506 : Nat := 1460598802598153090893361

theorem tailTrace_2844506 : CollatzResearch.WordTrace tailWord_2844506 prefixEnd_2844506 1460598802598153090893361 := by
  unfold tailWord_2844506
  simp only [CollatzResearch.WordTrace]
  refine ⟨25936914258212009948290343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69165104688565359862107581 25936914258212009948290343)
  ·
    refine ⟨38905371387318014922435515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25936914258212009948290343 38905371387318014922435515)
    ·
      refine ⟨58358057080977022383653273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38905371387318014922435515 58358057080977022383653273)
      ·
        refine ⟨43768542810732766787739955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58358057080977022383653273 43768542810732766787739955)
        ·
          refine ⟨65652814216099150181609933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43768542810732766787739955 65652814216099150181609933)
          ·
            refine ⟨24619805331037181318103725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65652814216099150181609933 24619805331037181318103725)
            ·
              refine ⟨9232426999138942994288897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24619805331037181318103725 9232426999138942994288897)
              ·
                refine ⟨6924320249354207245716673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9232426999138942994288897 6924320249354207245716673)
                ·
                  refine ⟨5193240187015655434287505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6924320249354207245716673 5193240187015655434287505)
                  ·
                    refine ⟨3894930140261741575715629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5193240187015655434287505 3894930140261741575715629)
                    ·
                      refine ⟨1460598802598153090893361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3894930140261741575715629 1460598802598153090893361)
                      ·
                        rfl

theorem cell23_2844506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_2844506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844506 prefixEnd_2844506 := by exact prefixLift 2844506
  have htrace : WordTrace (prefixWord ++ tailWord_2844506) baseStart_2844506 baseEnd_2844506 := by
    simpa [prefixWord, tailWord_2844506, baseEnd_2844506] using wordTrace_append hprefix tailTrace_2844506
  have hstable : (prefixWord ++ tailWord_2844506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844506).length < 2 ^ (prefixWord ++ tailWord_2844506).sum := by decide
  have hdescent : baseEnd_2844506 < baseStart_2844506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844576 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 2, 6, 2]
def baseStart_2844576 : Nat := 118140960795 + 2844576 * 2 ^ 59
def prefixEnd_2844576 : Nat := 4983230072969 + 3 ^ 40 * 2844576 * 2
def baseEnd_2844576 : Nat := 1460634746243967817018039

theorem tailTrace_2844576 : CollatzResearch.WordTrace tailWord_2844576 prefixEnd_2844576 1460634746243967817018039 := by
  unfold tailWord_2844576
  simp only [CollatzResearch.WordTrace]
  refine ⟨51875105071297220874104791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69166806761729627832139721 51875105071297220874104791)
  ·
    refine ⟨77812657606945831311157187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51875105071297220874104791 77812657606945831311157187)
    ·
      refine ⟨116718986410418746966735781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77812657606945831311157187 116718986410418746966735781)
      ·
        refine ⟨21884809951953515056262959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116718986410418746966735781 21884809951953515056262959)
        ·
          refine ⟨32827214927930272584394439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21884809951953515056262959 32827214927930272584394439)
          ·
            refine ⟨49240822391895408876591659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32827214927930272584394439 49240822391895408876591659)
            ·
              refine ⟨73861233587843113314887489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49240822391895408876591659 73861233587843113314887489)
              ·
                refine ⟨55395925190882334986165617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73861233587843113314887489 55395925190882334986165617)
                ·
                  refine ⟨41546943893161751239624213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55395925190882334986165617 41546943893161751239624213)
                  ·
                    refine ⟨1947512994991957089357385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41546943893161751239624213 1947512994991957089357385)
                    ·
                      refine ⟨1460634746243967817018039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1947512994991957089357385 1460634746243967817018039)
                      ·
                        rfl

theorem cell23_2844576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_2844576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844576 prefixEnd_2844576 := by exact prefixLift 2844576
  have htrace : WordTrace (prefixWord ++ tailWord_2844576) baseStart_2844576 baseEnd_2844576 := by
    simpa [prefixWord, tailWord_2844576, baseEnd_2844576] using wordTrace_append hprefix tailTrace_2844576
  have hstable : (prefixWord ++ tailWord_2844576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844576).length < 2 ^ (prefixWord ++ tailWord_2844576).sum := by decide
  have hdescent : baseEnd_2844576 < baseStart_2844576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844579 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 5]
def baseStart_2844579 : Nat := 118140960795 + 2844579 * 2 ^ 59
def prefixEnd_2844579 : Nat := 4983230072969 + 3 ^ 40 * 2844579 * 2
def baseEnd_2844579 : Nat := 1460636286685931305280525

theorem tailTrace_2844579 : CollatzResearch.WordTrace tailWord_2844579 prefixEnd_2844579 1460636286685931305280525 := by
  unfold tailWord_2844579
  simp only [CollatzResearch.WordTrace]
  refine ⟨103750319561583573260568791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69166879707722382173712527 103750319561583573260568791)
  ·
    refine ⟨155625479342375359890853187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103750319561583573260568791 155625479342375359890853187)
    ·
      refine ⟨233438219013563039836279781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155625479342375359890853187 233438219013563039836279781)
      ·
        refine ⟨43769666065043069969302459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233438219013563039836279781 43769666065043069969302459)
        ·
          refine ⟨65654499097564604953953689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43769666065043069969302459 65654499097564604953953689)
          ·
            refine ⟨49240874323173453715465267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65654499097564604953953689 49240874323173453715465267)
            ·
              refine ⟨73861311484760180573197901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49240874323173453715465267 73861311484760180573197901)
              ·
                refine ⟨27697991806785067714949213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73861311484760180573197901 27697991806785067714949213)
                ·
                  refine ⟨10386746927544400393105955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27697991806785067714949213 10386746927544400393105955)
                  ·
                    refine ⟨15580120391316600589658933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10386746927544400393105955 15580120391316600589658933)
                    ·
                      refine ⟨1460636286685931305280525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15580120391316600589658933 1460636286685931305280525)
                      ·
                        rfl

theorem cell23_2844579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_2844579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844579 prefixEnd_2844579 := by exact prefixLift 2844579
  have htrace : WordTrace (prefixWord ++ tailWord_2844579) baseStart_2844579 baseEnd_2844579 := by
    simpa [prefixWord, tailWord_2844579, baseEnd_2844579] using wordTrace_append hprefix tailTrace_2844579
  have hstable : (prefixWord ++ tailWord_2844579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844579).length < 2 ^ (prefixWord ++ tailWord_2844579).sum := by decide
  have hdescent : baseEnd_2844579 < baseStart_2844579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844604 : List Nat := [2, 2, 2, 5, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2844604 : Nat := 118140960795 + 2844604 * 2 ^ 59
def prefixEnd_2844604 : Nat := 4983230072969 + 3 ^ 40 * 2844604 * 2
def baseEnd_2844604 : Nat := 1460649123702293707467911

theorem tailTrace_2844604 : CollatzResearch.WordTrace tailWord_2844604 prefixEnd_2844604 1460649123702293707467911 := by
  unfold tailWord_2844604
  simp only [CollatzResearch.WordTrace]
  refine ⟨51875615693246501265114433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69167487590995335020152577 51875615693246501265114433)
  ·
    refine ⟨38906711769934875948835825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51875615693246501265114433 38906711769934875948835825)
    ·
      refine ⟨29180033827451156961626869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38906711769934875948835825 29180033827451156961626869)
      ·
        refine ⟨2735628171323545965152519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29180033827451156961626869 2735628171323545965152519)
        ·
          refine ⟨4103442256985318947728779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2735628171323545965152519 4103442256985318947728779)
          ·
            refine ⟨6155163385477978421593169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103442256985318947728779 6155163385477978421593169)
            ·
              refine ⟨4616372539108483816194877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6155163385477978421593169 4616372539108483816194877)
              ·
                refine ⟨1731139702165681431073079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4616372539108483816194877 1731139702165681431073079)
                ·
                  refine ⟨2596709553248522146609619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1731139702165681431073079 2596709553248522146609619)
                  ·
                    refine ⟨3895064329872783219914429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2596709553248522146609619 3895064329872783219914429)
                    ·
                      refine ⟨1460649123702293707467911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3895064329872783219914429 1460649123702293707467911)
                      ·
                        rfl

theorem cell23_2844604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2844604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844604 prefixEnd_2844604 := by exact prefixLift 2844604
  have htrace : WordTrace (prefixWord ++ tailWord_2844604) baseStart_2844604 baseEnd_2844604 := by
    simpa [prefixWord, tailWord_2844604, baseEnd_2844604] using wordTrace_append hprefix tailTrace_2844604
  have hstable : (prefixWord ++ tailWord_2844604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844604).length < 2 ^ (prefixWord ++ tailWord_2844604).sum := by decide
  have hdescent : baseEnd_2844604 < baseStart_2844604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844620 : List Nat := [2, 2, 1, 4, 1, 4, 1, 2, 2, 4]
def baseStart_2844620 : Nat := 118140960795 + 2844620 * 2 ^ 59
def prefixEnd_2844620 : Nat := 4983230072969 + 3 ^ 40 * 2844620 * 2
def baseEnd_2844620 : Nat := 486885779797588548289279

theorem tailTrace_2844620 : CollatzResearch.WordTrace tailWord_2844620 prefixEnd_2844620 486885779797588548289279 := by
  unfold tailWord_2844620
  simp only [CollatzResearch.WordTrace]
  refine ⟨51875907477217518631405657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69167876636290024841874209 51875907477217518631405657)
  ·
    refine ⟨38906930607913138973554243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51875907477217518631405657 38906930607913138973554243)
    ·
      refine ⟨58360395911869708460331365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38906930607913138973554243 58360395911869708460331365)
      ·
        refine ⟨10942574233475570336312131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58360395911869708460331365 10942574233475570336312131)
        ·
          refine ⟨16413861350213355504468197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10942574233475570336312131 16413861350213355504468197)
          ·
            refine ⟨3077599003165004157087787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16413861350213355504468197 3077599003165004157087787)
            ·
              refine ⟨4616398504747506235631681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3077599003165004157087787 4616398504747506235631681)
              ·
                refine ⟨3462298878560629676723761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4616398504747506235631681 3462298878560629676723761)
                ·
                  refine ⟨2596724158920472257542821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3462298878560629676723761 2596724158920472257542821)
                  ·
                    refine ⟨486885779797588548289279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2596724158920472257542821 486885779797588548289279)
                    ·
                      rfl

theorem cell23_2844620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_2844620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844620 prefixEnd_2844620 := by exact prefixLift 2844620
  have htrace : WordTrace (prefixWord ++ tailWord_2844620) baseStart_2844620 baseEnd_2844620 := by
    simpa [prefixWord, tailWord_2844620, baseEnd_2844620] using wordTrace_append hprefix tailTrace_2844620
  have hstable : (prefixWord ++ tailWord_2844620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844620).length < 2 ^ (prefixWord ++ tailWord_2844620).sum := by decide
  have hdescent : baseEnd_2844620 < baseStart_2844620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844630 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_2844630 : Nat := 118140960795 + 2844630 * 2 ^ 59
def prefixEnd_2844630 : Nat := 4983230072969 + 3 ^ 40 * 2844630 * 2
def baseEnd_2844630 : Nat := 1460662474199310605742791

theorem tailTrace_2844630 : CollatzResearch.WordTrace tailWord_2844630 prefixEnd_2844630 1460662474199310605742791 := by
  unfold tailWord_2844630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6484511230274925560667209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69168119789599205980450229 6484511230274925560667209)
  ·
    refine ⟨4863383422706194170500407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6484511230274925560667209 4863383422706194170500407)
    ·
      refine ⟨7295075134059291255750611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4863383422706194170500407 7295075134059291255750611)
      ·
        refine ⟨10942612701088936883625917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7295075134059291255750611 10942612701088936883625917)
        ·
          refine ⟨4103479762908351331359719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10942612701088936883625917 4103479762908351331359719)
          ·
            refine ⟨6155219644362526997039579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103479762908351331359719 6155219644362526997039579)
            ·
              refine ⟨9232829466543790495559369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6155219644362526997039579 9232829466543790495559369)
              ·
                refine ⟨6924622099907842871669527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9232829466543790495559369 6924622099907842871669527)
                ·
                  refine ⟨10386933149861764307504291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6924622099907842871669527 10386933149861764307504291)
                  ·
                    refine ⟨15580399724792646461256437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10386933149861764307504291 15580399724792646461256437)
                    ·
                      refine ⟨1460662474199310605742791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15580399724792646461256437 1460662474199310605742791)
                      ·
                        rfl

theorem cell23_2844630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_2844630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844630 prefixEnd_2844630 := by exact prefixLift 2844630
  have htrace : WordTrace (prefixWord ++ tailWord_2844630) baseStart_2844630 baseEnd_2844630 := by
    simpa [prefixWord, tailWord_2844630, baseEnd_2844630] using wordTrace_append hprefix tailTrace_2844630
  have hstable : (prefixWord ++ tailWord_2844630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844630).length < 2 ^ (prefixWord ++ tailWord_2844630).sum := by decide
  have hdescent : baseEnd_2844630 < baseStart_2844630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844637 : List Nat := [1, 4, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2844637 : Nat := 118140960795 + 2844637 * 2 ^ 59
def prefixEnd_2844637 : Nat := 4983230072969 + 3 ^ 40 * 2844637 * 2
def baseEnd_2844637 : Nat := 486888689521297359451753

theorem tailTrace_2844637 : CollatzResearch.WordTrace tailWord_2844637 prefixEnd_2844637 486888689521297359451753 := by
  unfold tailWord_2844637
  simp only [CollatzResearch.WordTrace]
  refine ⟨103752434995373449166180165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69168289996915632777453443 103752434995373449166180165)
  ·
    refine ⟨19453581561632521718658781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103752434995373449166180165 19453581561632521718658781)
    ·
      refine ⟨7295093085612195644497043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19453581561632521718658781 7295093085612195644497043)
      ·
        refine ⟨10942639628418293466745565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7295093085612195644497043 10942639628418293466745565)
        ·
          refine ⟨4103489860656860050029587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10942639628418293466745565 4103489860656860050029587)
          ·
            refine ⟨6155234790985290075044381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103489860656860050029587 6155234790985290075044381)
            ·
              refine ⟨2308213046619483778141643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6155234790985290075044381 2308213046619483778141643)
              ·
                refine ⟨3462319569929225667212465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2308213046619483778141643 3462319569929225667212465)
                ·
                  refine ⟨2596739677446919250409349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3462319569929225667212465 2596739677446919250409349)
                  ·
                    refine ⟨486888689521297359451753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2596739677446919250409349 486888689521297359451753)
                    ·
                      rfl

theorem cell23_2844637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2844637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844637 prefixEnd_2844637 := by exact prefixLift 2844637
  have htrace : WordTrace (prefixWord ++ tailWord_2844637) baseStart_2844637 baseEnd_2844637 := by
    simpa [prefixWord, tailWord_2844637, baseEnd_2844637] using wordTrace_append hprefix tailTrace_2844637
  have hstable : (prefixWord ++ tailWord_2844637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844637).length < 2 ^ (prefixWord ++ tailWord_2844637).sum := by decide
  have hdescent : baseEnd_2844637 < baseStart_2844637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844643 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 3]
def baseStart_2844643 : Nat := 118140960795 + 2844643 * 2 ^ 59
def prefixEnd_2844643 : Nat := 4983230072969 + 3 ^ 40 * 2844643 * 2
def baseEnd_2844643 : Nat := 1460669149447819054880231

theorem tailTrace_2844643 : CollatzResearch.WordTrace tailWord_2844643 prefixEnd_2844643 1460669149447819054880231 := by
  unfold tailWord_2844643
  simp only [CollatzResearch.WordTrace]
  refine ⟨103752653833351712190898583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69168435888901141460599055 103752653833351712190898583)
  ·
    refine ⟨155628980750027568286347875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103752653833351712190898583 155628980750027568286347875)
    ·
      refine ⟨233443471125041352429521813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155628980750027568286347875 233443471125041352429521813)
      ·
        refine ⟨10942662708986313395133835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 233443471125041352429521813 10942662708986313395133835)
        ·
          refine ⟨16413994063479470092700753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10942662708986313395133835 16413994063479470092700753)
          ·
            refine ⟨12310495547609602569525565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16413994063479470092700753 12310495547609602569525565)
            ·
              refine ⟨4616435830353600963572087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12310495547609602569525565 4616435830353600963572087)
              ·
                refine ⟨6924653745530401445358131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4616435830353600963572087 6924653745530401445358131)
                ·
                  refine ⟨10386980618295602168037197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6924653745530401445358131 10386980618295602168037197)
                  ·
                    refine ⟨3895117731860850813013949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10386980618295602168037197 3895117731860850813013949)
                    ·
                      refine ⟨1460669149447819054880231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3895117731860850813013949 1460669149447819054880231)
                      ·
                        rfl

theorem cell23_2844643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_2844643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844643 prefixEnd_2844643 := by exact prefixLift 2844643
  have htrace : WordTrace (prefixWord ++ tailWord_2844643) baseStart_2844643 baseEnd_2844643 := by
    simpa [prefixWord, tailWord_2844643, baseEnd_2844643] using wordTrace_append hprefix tailTrace_2844643
  have hstable : (prefixWord ++ tailWord_2844643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844643).length < 2 ^ (prefixWord ++ tailWord_2844643).sum := by decide
  have hdescent : baseEnd_2844643 < baseStart_2844643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844659 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 1, 8]
def baseStart_2844659 : Nat := 118140960795 + 2844659 * 2 ^ 59
def prefixEnd_2844659 : Nat := 4983230072969 + 3 ^ 40 * 2844659 * 2
def baseEnd_2844659 : Nat := 486892455046096997426719

theorem tailTrace_2844659 : CollatzResearch.WordTrace tailWord_2844659 prefixEnd_2844659 486892455046096997426719 := by
  unfold tailWord_2844659
  simp only [CollatzResearch.WordTrace]
  refine ⟨103753237401293746923481031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69168824934195831282320687 103753237401293746923481031)
  ·
    refine ⟨155629856101940620385221547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103753237401293746923481031 155629856101940620385221547)
    ·
      refine ⟨233444784152910930577832321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155629856101940620385221547 233444784152910930577832321)
      ·
        refine ⟨175083588114683197933374241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233444784152910930577832321 175083588114683197933374241)
        ·
          refine ⟨131312691086012398450030681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175083588114683197933374241 131312691086012398450030681)
          ·
            refine ⟨98484518314509298837523011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131312691086012398450030681 98484518314509298837523011)
            ·
              refine ⟨147726777471763948256284517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98484518314509298837523011 147726777471763948256284517)
              ·
                refine ⟨27698770775955740298053347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147726777471763948256284517 27698770775955740298053347)
                ·
                  refine ⟨41548156163933610447080021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27698770775955740298053347 41548156163933610447080021)
                  ·
                    refine ⟨486892455046096997426719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41548156163933610447080021 486892455046096997426719)
                    ·
                      rfl

theorem cell23_2844659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 8].length) (baseStart_2844659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844659 prefixEnd_2844659 := by exact prefixLift 2844659
  have htrace : WordTrace (prefixWord ++ tailWord_2844659) baseStart_2844659 baseEnd_2844659 := by
    simpa [prefixWord, tailWord_2844659, baseEnd_2844659] using wordTrace_append hprefix tailTrace_2844659
  have hstable : (prefixWord ++ tailWord_2844659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844659).length < 2 ^ (prefixWord ++ tailWord_2844659).sum := by decide
  have hdescent : baseEnd_2844659 < baseStart_2844659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844686 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2844686 : Nat := 118140960795 + 2844686 * 2 ^ 59
def prefixEnd_2844686 : Nat := 4983230072969 + 3 ^ 40 * 2844686 * 2
def baseEnd_2844686 : Nat := 1460691229115962386642533

theorem tailTrace_2844686 : CollatzResearch.WordTrace tailWord_2844686 prefixEnd_2844686 1460691229115962386642533 := by
  unfold tailWord_2844686
  simp only [CollatzResearch.WordTrace]
  refine ⟨12969277771524491316839239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69169481448130620356475941 12969277771524491316839239)
  ·
    refine ⟨19453916657286736975258859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12969277771524491316839239 19453916657286736975258859)
    ·
      refine ⟨29180874985930105462888289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19453916657286736975258859 29180874985930105462888289)
      ·
        refine ⟨21885656239447579097166217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29180874985930105462888289 21885656239447579097166217)
        ·
          refine ⟨16414242179585684322874663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21885656239447579097166217 16414242179585684322874663)
          ·
            refine ⟨24621363269378526484311995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16414242179585684322874663 24621363269378526484311995)
            ·
              refine ⟨36932044904067789726467993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24621363269378526484311995 36932044904067789726467993)
              ·
                refine ⟨27699033678050842294850995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36932044904067789726467993 27699033678050842294850995)
                ·
                  refine ⟨41548550517076263442276493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27699033678050842294850995 41548550517076263442276493)
                  ·
                    refine ⟨15580706443903598790853685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41548550517076263442276493 15580706443903598790853685)
                    ·
                      refine ⟨1460691229115962386642533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15580706443903598790853685 1460691229115962386642533)
                      ·
                        rfl

theorem cell23_2844686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2844686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844686 prefixEnd_2844686 := by exact prefixLift 2844686
  have htrace : WordTrace (prefixWord ++ tailWord_2844686) baseStart_2844686 baseEnd_2844686 := by
    simpa [prefixWord, tailWord_2844686, baseEnd_2844686] using wordTrace_append hprefix tailTrace_2844686
  have hstable : (prefixWord ++ tailWord_2844686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844686).length < 2 ^ (prefixWord ++ tailWord_2844686).sum := by decide
  have hdescent : baseEnd_2844686 < baseStart_2844686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844696 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_2844696 : Nat := 118140960795 + 2844696 * 2 ^ 59
def prefixEnd_2844696 : Nat := 4983230072969 + 3 ^ 40 * 2844696 * 2
def baseEnd_2844696 : Nat := 1460696363922507347517487

theorem tailTrace_2844696 : CollatzResearch.WordTrace tailWord_2844696 prefixEnd_2844696 1460696363922507347517487 := by
  unfold tailWord_2844696
  simp only [CollatzResearch.WordTrace]
  refine ⟨51877293451079851121288971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69169724601439801495051961 51877293451079851121288971)
  ·
    refine ⟨77815940176619776681933457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51877293451079851121288971 77815940176619776681933457)
    ·
      refine ⟨58361955132464832511450093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77815940176619776681933457 58361955132464832511450093)
      ·
        refine ⟨21885733174674312191793785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58361955132464832511450093 21885733174674312191793785)
        ·
          refine ⟨16414299881005734143845339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21885733174674312191793785 16414299881005734143845339)
          ·
            refine ⟨24621449821508601215768009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16414299881005734143845339 24621449821508601215768009)
            ·
              refine ⟨18466087366131450911826007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24621449821508601215768009 18466087366131450911826007)
              ·
                refine ⟨27699131049197176367739011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18466087366131450911826007 27699131049197176367739011)
                ·
                  refine ⟨41548696573795764551608517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27699131049197176367739011 41548696573795764551608517)
                  ·
                    refine ⟨7790380607586705853426597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41548696573795764551608517 7790380607586705853426597)
                    ·
                      refine ⟨1460696363922507347517487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7790380607586705853426597 1460696363922507347517487)
                      ·
                        rfl

theorem cell23_2844696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_2844696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844696 prefixEnd_2844696 := by exact prefixLift 2844696
  have htrace : WordTrace (prefixWord ++ tailWord_2844696) baseStart_2844696 baseEnd_2844696 := by
    simpa [prefixWord, tailWord_2844696, baseEnd_2844696] using wordTrace_append hprefix tailTrace_2844696
  have hstable : (prefixWord ++ tailWord_2844696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844696).length < 2 ^ (prefixWord ++ tailWord_2844696).sum := by decide
  have hdescent : baseEnd_2844696 < baseStart_2844696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844706 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 9]
def baseStart_2844706 : Nat := 118140960795 + 2844706 * 2 ^ 59
def prefixEnd_2844706 : Nat := 4983230072969 + 3 ^ 40 * 2844706 * 2
def baseEnd_2844706 : Nat := 162300166525450256488049

theorem tailTrace_2844706 : CollatzResearch.WordTrace tailWord_2844706 prefixEnd_2844706 162300166525450256488049 := by
  unfold tailWord_2844706
  simp only [CollatzResearch.WordTrace]
  refine ⟨25938737908030868487610493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69169967754748982633627981 25938737908030868487610493)
  ·
    refine ⟨9727026715511575682853935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25938737908030868487610493 9727026715511575682853935)
    ·
      refine ⟨14590540073267363524280903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9727026715511575682853935 14590540073267363524280903)
      ·
        refine ⟨21885810109901045286421355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14590540073267363524280903 21885810109901045286421355)
        ·
          refine ⟨32828715164851567929632033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21885810109901045286421355 32828715164851567929632033)
          ·
            refine ⟨24621536373638675947224025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32828715164851567929632033 24621536373638675947224025)
            ·
              refine ⟨18466152280229006960418019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24621536373638675947224025 18466152280229006960418019)
              ·
                refine ⟨27699228420343510440627029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18466152280229006960418019 27699228420343510440627029)
                ·
                  refine ⟨162300166525450256488049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27699228420343510440627029 162300166525450256488049)
                  ·
                    rfl

theorem cell23_2844706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_2844706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844706 prefixEnd_2844706 := by exact prefixLift 2844706
  have htrace : WordTrace (prefixWord ++ tailWord_2844706) baseStart_2844706 baseEnd_2844706 := by
    simpa [prefixWord, tailWord_2844706, baseEnd_2844706] using wordTrace_append hprefix tailTrace_2844706
  have hstable : (prefixWord ++ tailWord_2844706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844706).length < 2 ^ (prefixWord ++ tailWord_2844706).sum := by decide
  have hdescent : baseEnd_2844706 < baseStart_2844706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844716 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 3]
def baseStart_2844716 : Nat := 118140960795 + 2844716 * 2 ^ 59
def prefixEnd_2844716 : Nat := 4983230072969 + 3 ^ 40 * 2844716 * 2
def baseEnd_2844716 : Nat := 1460706633535597269267395

theorem tailTrace_2844716 : CollatzResearch.WordTrace tailWord_2844716 prefixEnd_2844716 1460706633535597269267395 := by
  unfold tailWord_2844716
  simp only [CollatzResearch.WordTrace]
  refine ⟨51877658181043622829153001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69170210908058163772204001 51877658181043622829153001)
  ·
    refine ⟨38908243635782717121864751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51877658181043622829153001 38908243635782717121864751)
    ·
      refine ⟨58362365453674075682797127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38908243635782717121864751 58362365453674075682797127)
      ·
        refine ⟨87543548180511113524195691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58362365453674075682797127 87543548180511113524195691)
        ·
          refine ⟨131315322270766670286293537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87543548180511113524195691 131315322270766670286293537)
          ·
            refine ⟨98486491703075002714720153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131315322270766670286293537 98486491703075002714720153)
            ·
              refine ⟨73864868777306252036040115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98486491703075002714720153 73864868777306252036040115)
              ·
                refine ⟨110797303165959378054060173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73864868777306252036040115 110797303165959378054060173)
                ·
                  refine ⟨41548988687234766770272565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110797303165959378054060173 41548988687234766770272565)
                  ·
                    refine ⟨3895217689428259384713053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41548988687234766770272565 3895217689428259384713053)
                    ·
                      refine ⟨1460706633535597269267395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3895217689428259384713053 1460706633535597269267395)
                      ·
                        rfl

theorem cell23_2844716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_2844716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844716 prefixEnd_2844716 := by exact prefixLift 2844716
  have htrace : WordTrace (prefixWord ++ tailWord_2844716) baseStart_2844716 baseEnd_2844716 := by
    simpa [prefixWord, tailWord_2844716, baseEnd_2844716] using wordTrace_append hprefix tailTrace_2844716
  have hstable : (prefixWord ++ tailWord_2844716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844716).length < 2 ^ (prefixWord ++ tailWord_2844716).sum := by decide
  have hdescent : baseEnd_2844716 < baseStart_2844716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844733 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_2844733 : Nat := 118140960795 + 2844733 * 2 ^ 59
def prefixEnd_2844733 : Nat := 4983230072969 + 3 ^ 40 * 2844733 * 2
def baseEnd_2844733 : Nat := 1460715362706723702754817

theorem tailTrace_2844733 : CollatzResearch.WordTrace tailWord_2844733 prefixEnd_2844733 1460715362706723702754817 := by
  unfold tailWord_2844733
  simp only [CollatzResearch.WordTrace]
  refine ⟨103755936403025657561674853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69170624268683771707783235 103755936403025657561674853)
  ·
    refine ⟨19454238075567310792814035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103755936403025657561674853 19454238075567310792814035)
    ·
      refine ⟨29181357113350966189221053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19454238075567310792814035 29181357113350966189221053)
      ·
        refine ⟨10943008917506612320957895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29181357113350966189221053 10943008917506612320957895)
        ·
          refine ⟨16414513376259918481436843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10943008917506612320957895 16414513376259918481436843)
          ·
            refine ⟨24621770064389877722155265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16414513376259918481436843 24621770064389877722155265)
            ·
              refine ⟨18466327548292408291616449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24621770064389877722155265 18466327548292408291616449)
              ·
                refine ⟨13849745661219306218712337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18466327548292408291616449 13849745661219306218712337)
                ·
                  refine ⟨10387309245914479664034253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13849745661219306218712337 10387309245914479664034253)
                  ·
                    refine ⟨3895240967217929874012845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10387309245914479664034253 3895240967217929874012845)
                    ·
                      refine ⟨1460715362706723702754817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3895240967217929874012845 1460715362706723702754817)
                      ·
                        rfl

theorem cell23_2844733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_2844733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844733 prefixEnd_2844733 := by exact prefixLift 2844733
  have htrace : WordTrace (prefixWord ++ tailWord_2844733) baseStart_2844733 baseEnd_2844733 := by
    simpa [prefixWord, tailWord_2844733, baseEnd_2844733] using wordTrace_append hprefix tailTrace_2844733
  have hstable : (prefixWord ++ tailWord_2844733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844733).length < 2 ^ (prefixWord ++ tailWord_2844733).sum := by decide
  have hdescent : baseEnd_2844733 < baseStart_2844733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844743 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 1, 7, 2]
def baseStart_2844743 : Nat := 118140960795 + 2844743 * 2 ^ 59
def prefixEnd_2844743 : Nat := 4983230072969 + 3 ^ 40 * 2844743 * 2
def baseEnd_2844743 : Nat := 1460720497513268663629771

theorem tailTrace_2844743 : CollatzResearch.WordTrace tailWord_2844743 prefixEnd_2844743 1460720497513268663629771 := by
  unfold tailWord_2844743
  simp only [CollatzResearch.WordTrace]
  refine ⟨103756301132989429269538883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69170867421992952846359255 103756301132989429269538883)
  ·
    refine ⟨155634451699484143904308325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103756301132989429269538883 155634451699484143904308325)
    ·
      refine ⟨29181459693653276982057811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155634451699484143904308325 29181459693653276982057811)
      ·
        refine ⟨43772189540479915473086717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29181459693653276982057811 43772189540479915473086717)
        ·
          refine ⟨16414571077679968302407519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43772189540479915473086717 16414571077679968302407519)
          ·
            refine ⟨24621856616519952453611279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16414571077679968302407519 24621856616519952453611279)
            ·
              refine ⟨36932784924779928680416919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24621856616519952453611279 36932784924779928680416919)
              ·
                refine ⟨55399177387169893020625379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36932784924779928680416919 55399177387169893020625379)
                ·
                  refine ⟨83098766080754839530938069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55399177387169893020625379 83098766080754839530938069)
                  ·
                    refine ⟨1947627330017691551506361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 83098766080754839530938069 1947627330017691551506361)
                    ·
                      refine ⟨1460720497513268663629771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1947627330017691551506361 1460720497513268663629771)
                      ·
                        rfl

theorem cell23_2844743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_2844743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844743 prefixEnd_2844743 := by exact prefixLift 2844743
  have htrace : WordTrace (prefixWord ++ tailWord_2844743) baseStart_2844743 baseEnd_2844743 := by
    simpa [prefixWord, tailWord_2844743, baseEnd_2844743] using wordTrace_append hprefix tailTrace_2844743
  have hstable : (prefixWord ++ tailWord_2844743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844743).length < 2 ^ (prefixWord ++ tailWord_2844743).sum := by decide
  have hdescent : baseEnd_2844743 < baseStart_2844743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844770 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_2844770 : Nat := 118140960795 + 2844770 * 2 ^ 59
def prefixEnd_2844770 : Nat := 4983230072969 + 3 ^ 40 * 2844770 * 2
def baseEnd_2844770 : Nat := 486911453830313352664049

theorem tailTrace_2844770 : CollatzResearch.WordTrace tailWord_2844770 prefixEnd_2844770 486911453830313352664049 := by
  unfold tailWord_2844770
  simp only [CollatzResearch.WordTrace]
  refine ⟨25939321475972903220192941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69171523935927741920514509 25939321475972903220192941)
  ·
    refine ⟨9727245553489838707572353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25939321475972903220192941 9727245553489838707572353)
    ·
      refine ⟨7295434165117379030679265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9727245553489838707572353 7295434165117379030679265)
      ·
        refine ⟨5471575623838034273009449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7295434165117379030679265 5471575623838034273009449)
        ·
          refine ⟨4103681717878525704757087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5471575623838034273009449 4103681717878525704757087)
          ·
            refine ⟨6155522576817788557135631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103681717878525704757087 6155522576817788557135631)
            ·
              refine ⟨9233283865226682835703447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6155522576817788557135631 9233283865226682835703447)
              ·
                refine ⟨13849925797840024253555171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9233283865226682835703447 13849925797840024253555171)
                ·
                  refine ⟨20774888696760036380332757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13849925797840024253555171 20774888696760036380332757)
                  ·
                    refine ⟨486911453830313352664049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20774888696760036380332757 486911453830313352664049)
                    ·
                      rfl

theorem cell23_2844770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_2844770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844770 prefixEnd_2844770 := by exact prefixLift 2844770
  have htrace : WordTrace (prefixWord ++ tailWord_2844770) baseStart_2844770 baseEnd_2844770 := by
    simpa [prefixWord, tailWord_2844770, baseEnd_2844770] using wordTrace_append hprefix tailTrace_2844770
  have hstable : (prefixWord ++ tailWord_2844770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844770).length < 2 ^ (prefixWord ++ tailWord_2844770).sum := by decide
  have hdescent : baseEnd_2844770 < baseStart_2844770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844773 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_2844773 : Nat := 118140960795 + 2844773 * 2 ^ 59
def prefixEnd_2844773 : Nat := 4983230072969 + 3 ^ 40 * 2844773 * 2
def baseEnd_2844773 : Nat := 1460735901932903546254633

theorem tailTrace_2844773 : CollatzResearch.WordTrace tailWord_2844773 prefixEnd_2844773 1460735901932903546254633 := by
  unfold tailWord_2844773
  simp only [CollatzResearch.WordTrace]
  refine ⟨103757395322880744393130973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69171596881920496262087315 103757395322880744393130973)
  ·
    refine ⟨38909023246080279147424115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103757395322880744393130973 38909023246080279147424115)
    ·
      refine ⟨58363534869120418721136173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38909023246080279147424115 58363534869120418721136173)
      ·
        refine ⟨21886325575920157020426065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58363534869120418721136173 21886325575920157020426065)
        ·
          refine ⟨16414744181940117765319549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21886325575920157020426065 16414744181940117765319549)
          ·
            refine ⟨6155529068227544161994831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16414744181940117765319549 6155529068227544161994831)
            ·
              refine ⟨9233293602341316242992247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6155529068227544161994831 9233293602341316242992247)
              ·
                refine ⟨13849940403511974364488371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9233293602341316242992247 13849940403511974364488371)
                ·
                  refine ⟨20774910605267961546732557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13849940403511974364488371 20774910605267961546732557)
                  ·
                    refine ⟨7790591476975485580024709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20774910605267961546732557 7790591476975485580024709)
                    ·
                      refine ⟨1460735901932903546254633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7790591476975485580024709 1460735901932903546254633)
                      ·
                        rfl

theorem cell23_2844773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_2844773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844773 prefixEnd_2844773 := by exact prefixLift 2844773
  have htrace : WordTrace (prefixWord ++ tailWord_2844773) baseStart_2844773 baseEnd_2844773 := by
    simpa [prefixWord, tailWord_2844773, baseEnd_2844773] using wordTrace_append hprefix tailTrace_2844773
  have hstable : (prefixWord ++ tailWord_2844773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844773).length < 2 ^ (prefixWord ++ tailWord_2844773).sum := by decide
  have hdescent : baseEnd_2844773 < baseStart_2844773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844816 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 6]
def baseStart_2844816 : Nat := 118140960795 + 2844816 * 2 ^ 59
def prefixEnd_2844816 : Nat := 4983230072969 + 3 ^ 40 * 2844816 * 2
def baseEnd_2844816 : Nat := 1460757981601046878016935

theorem tailTrace_2844816 : CollatzResearch.WordTrace tailWord_2844816 prefixEnd_2844816 1460757981601046878016935 := by
  unfold tailWord_2844816
  simp only [CollatzResearch.WordTrace]
  refine ⟨51879481830862481368473151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69172642441149975157964201 51879481830862481368473151)
  ·
    refine ⟨77819222746293722052709727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51879481830862481368473151 77819222746293722052709727)
    ·
      refine ⟨116728834119440583079064591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77819222746293722052709727 116728834119440583079064591)
      ·
        refine ⟨175093251179160874618596887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116728834119440583079064591 175093251179160874618596887)
        ·
          refine ⟨262639876768741311927895331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175093251179160874618596887 262639876768741311927895331)
          ·
            refine ⟨393959815153111967891842997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262639876768741311927895331 393959815153111967891842997)
            ·
              refine ⟨36933732670604246989860281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 393959815153111967891842997 36933732670604246989860281)
              ·
                refine ⟨27700299502953185242395211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36933732670604246989860281 27700299502953185242395211)
                ·
                  refine ⟨41550449254429777863592817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27700299502953185242395211 41550449254429777863592817)
                  ·
                    refine ⟨31162836940822333397694613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41550449254429777863592817 31162836940822333397694613)
                    ·
                      refine ⟨1460757981601046878016935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31162836940822333397694613 1460757981601046878016935)
                      ·
                        rfl

theorem cell23_2844816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_2844816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844816 prefixEnd_2844816 := by exact prefixLift 2844816
  have htrace : WordTrace (prefixWord ++ tailWord_2844816) baseStart_2844816 baseEnd_2844816 := by
    simpa [prefixWord, tailWord_2844816, baseEnd_2844816] using wordTrace_append hprefix tailTrace_2844816
  have hstable : (prefixWord ++ tailWord_2844816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844816).length < 2 ^ (prefixWord ++ tailWord_2844816).sum := by decide
  have hdescent : baseEnd_2844816 < baseStart_2844816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844834 : List Nat := [3, 3, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_2844834 : Nat := 118140960795 + 2844834 * 2 ^ 59
def prefixEnd_2844834 : Nat := 4983230072969 + 3 ^ 40 * 2844834 * 2
def baseEnd_2844834 : Nat := 486922408084275935863951

theorem tailTrace_2844834 : CollatzResearch.WordTrace tailWord_2844834 prefixEnd_2844834 486922408084275935863951 := by
  unfold tailWord_2844834
  simp only [CollatzResearch.WordTrace]
  refine ⟨25939905043914937952775389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69173080117106501207401037 25939905043914937952775389)
  ·
    refine ⟨9727464391468101732290771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25939905043914937952775389 9727464391468101732290771)
    ·
      refine ⟨14591196587202152598436157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9727464391468101732290771 14591196587202152598436157)
      ·
        refine ⟨5471698720200807224413559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14591196587202152598436157 5471698720200807224413559)
        ·
          refine ⟨8207548080301210836620339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5471698720200807224413559 8207548080301210836620339)
          ·
            refine ⟨12311322120451816254930509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8207548080301210836620339 12311322120451816254930509)
            ·
              refine ⟨4616745795169431095598941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12311322120451816254930509 4616745795169431095598941)
              ·
                refine ⟨1731279673188536660849603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4616745795169431095598941 1731279673188536660849603)
                ·
                  refine ⟨2596919509782804991274405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1731279673188536660849603 2596919509782804991274405)
                  ·
                    refine ⟨486922408084275935863951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2596919509782804991274405 486922408084275935863951)
                    ·
                      rfl

theorem cell23_2844834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_2844834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844834 prefixEnd_2844834 := by exact prefixLift 2844834
  have htrace : WordTrace (prefixWord ++ tailWord_2844834) baseStart_2844834 baseEnd_2844834 := by
    simpa [prefixWord, tailWord_2844834, baseEnd_2844834] using wordTrace_append hprefix tailTrace_2844834
  have hstable : (prefixWord ++ tailWord_2844834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844834).length < 2 ^ (prefixWord ++ tailWord_2844834).sum := by decide
  have hdescent : baseEnd_2844834 < baseStart_2844834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844863 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 4]
def baseStart_2844863 : Nat := 118140960795 + 2844863 * 2 ^ 59
def prefixEnd_2844863 : Nat := 4983230072969 + 3 ^ 40 * 2844863 * 2
def baseEnd_2844863 : Nat := 1460782115191808194129219

theorem tailTrace_2844863 : CollatzResearch.WordTrace tailWord_2844863 prefixEnd_2844863 1460782115191808194129219 := by
  unfold tailWord_2844863
  simp only [CollatzResearch.WordTrace]
  refine ⟨103760677892554689763907243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69173785261703126509271495 103760677892554689763907243)
  ·
    refine ⟨155641016838832034645860865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103760677892554689763907243 155641016838832034645860865)
    ·
      refine ⟨116730762629124025984395649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155641016838832034645860865 116730762629124025984395649)
      ·
        refine ⟨87548071971843019488296737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116730762629124025984395649 87548071971843019488296737)
        ·
          refine ⟨65661053978882264616222553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87548071971843019488296737 65661053978882264616222553)
          ·
            refine ⟨49245790484161698462166915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65661053978882264616222553 49245790484161698462166915)
            ·
              refine ⟨73868685726242547693250373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49245790484161698462166915 73868685726242547693250373)
              ·
                refine ⟨13850378573670477692484445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73868685726242547693250373 13850378573670477692484445)
                ·
                  refine ⟨5193891965126429134681667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13850378573670477692484445 5193891965126429134681667)
                  ·
                    refine ⟨7790837947689643702022501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5193891965126429134681667 7790837947689643702022501)
                    ·
                      refine ⟨1460782115191808194129219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7790837947689643702022501 1460782115191808194129219)
                      ·
                        rfl

theorem cell23_2844863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_2844863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844863 prefixEnd_2844863 := by exact prefixLift 2844863
  have htrace : WordTrace (prefixWord ++ tailWord_2844863) baseStart_2844863 baseEnd_2844863 := by
    simpa [prefixWord, tailWord_2844863, baseEnd_2844863] using wordTrace_append hprefix tailTrace_2844863
  have hstable : (prefixWord ++ tailWord_2844863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844863).length < 2 ^ (prefixWord ++ tailWord_2844863).sum := by decide
  have hdescent : baseEnd_2844863 < baseStart_2844863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844873 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 6, 4]
def baseStart_2844873 : Nat := 118140960795 + 2844873 * 2 ^ 59
def prefixEnd_2844873 : Nat := 4983230072969 + 3 ^ 40 * 2844873 * 2
def baseEnd_2844873 : Nat := 486929083332784385001391

theorem tailTrace_2844873 : CollatzResearch.WordTrace tailWord_2844873 prefixEnd_2844873 486929083332784385001391 := by
  unfold tailWord_2844873
  simp only [CollatzResearch.WordTrace]
  refine ⟨103761042622518461471771273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69174028415012307647847515 103761042622518461471771273)
  ·
    refine ⟨77820781966888846103828455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103761042622518461471771273 77820781966888846103828455)
    ·
      refine ⟨116731172950333269155742683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77820781966888846103828455 116731172950333269155742683)
      ·
        refine ⟨175096759425499903733614025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116731172950333269155742683 175096759425499903733614025)
        ·
          refine ⟨131322569569124927800210519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175096759425499903733614025 131322569569124927800210519)
          ·
            refine ⟨196983854353687391700315779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131322569569124927800210519 196983854353687391700315779)
            ·
              refine ⟨295475781530531087550473669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196983854353687391700315779 295475781530531087550473669)
              ·
                refine ⟨55401709036974578915713813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295475781530531087550473669 55401709036974578915713813)
                ·
                  refine ⟨2596955111108183386674085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55401709036974578915713813 2596955111108183386674085)
                  ·
                    refine ⟨486929083332784385001391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2596955111108183386674085 486929083332784385001391)
                    ·
                      rfl

theorem cell23_2844873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 4].length) (baseStart_2844873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844873 prefixEnd_2844873 := by exact prefixLift 2844873
  have htrace : WordTrace (prefixWord ++ tailWord_2844873) baseStart_2844873 baseEnd_2844873 := by
    simpa [prefixWord, tailWord_2844873, baseEnd_2844873] using wordTrace_append hprefix tailTrace_2844873
  have hstable : (prefixWord ++ tailWord_2844873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844873).length < 2 ^ (prefixWord ++ tailWord_2844873).sum := by decide
  have hdescent : baseEnd_2844873 < baseStart_2844873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844897 : List Nat := [1, 2, 3, 1, 3, 1, 5, 1, 1, 1, 4]
def baseStart_2844897 : Nat := 118140960795 + 2844897 * 2 ^ 59
def prefixEnd_2844897 : Nat := 4983230072969 + 3 ^ 40 * 2844897 * 2
def baseEnd_2844897 : Nat := 1460799573534061061104063

theorem tailTrace_2844897 : CollatzResearch.WordTrace tailWord_2844897 prefixEnd_2844897 1460799573534061061104063 := by
  unfold tailWord_2844897
  simp only [CollatzResearch.WordTrace]
  refine ⟨103761917974431513570644945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69174611982954342380429963 103761917974431513570644945)
  ·
    refine ⟨77821438480823635177983709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103761917974431513570644945 77821438480823635177983709)
    ·
      refine ⟨29183039430308863191743891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77821438480823635177983709 29183039430308863191743891)
      ·
        refine ⟨43774559145463294787615837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29183039430308863191743891 43774559145463294787615837)
        ·
          refine ⟨16415459679548735545355939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43774559145463294787615837 16415459679548735545355939)
          ·
            refine ⟨24623189519323103318033909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16415459679548735545355939 24623189519323103318033909)
            ·
              refine ⟨2308424017436540936065679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24623189519323103318033909 2308424017436540936065679)
              ·
                refine ⟨3462636026154811404098519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2308424017436540936065679 3462636026154811404098519)
                ·
                  refine ⟨5193954039232217106147779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3462636026154811404098519 5193954039232217106147779)
                  ·
                    refine ⟨7790931058848325659221669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5193954039232217106147779 7790931058848325659221669)
                    ·
                      refine ⟨1460799573534061061104063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7790931058848325659221669 1460799573534061061104063)
                      ·
                        rfl

theorem cell23_2844897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_2844897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844897 prefixEnd_2844897 := by exact prefixLift 2844897
  have htrace : WordTrace (prefixWord ++ tailWord_2844897) baseStart_2844897 baseEnd_2844897 := by
    simpa [prefixWord, tailWord_2844897, baseEnd_2844897] using wordTrace_append hprefix tailTrace_2844897
  have hstable : (prefixWord ++ tailWord_2844897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844897).length < 2 ^ (prefixWord ++ tailWord_2844897).sum := by decide
  have hdescent : baseEnd_2844897 < baseStart_2844897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844903 : List Nat := [1, 1, 5, 3, 1, 12]
def baseStart_2844903 : Nat := 118140960795 + 2844903 * 2 ^ 59
def prefixEnd_2844903 : Nat := 4983230072969 + 3 ^ 40 * 2844903 * 2
def baseEnd_2844903 : Nat := 6011533557275670936745

theorem tailTrace_2844903 : CollatzResearch.WordTrace tailWord_2844903 prefixEnd_2844903 6011533557275670936745 := by
  unfold tailWord_2844903
  simp only [CollatzResearch.WordTrace]
  refine ⟨103762136812409776595363363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69174757874939851063575575 103762136812409776595363363)
  ·
    refine ⟨155643205218614664893045045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103762136812409776595363363 155643205218614664893045045)
    ·
      refine ⟨14591550489245124833722973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155643205218614664893045045 14591550489245124833722973)
      ·
        refine ⟨5471831433466921812646115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14591550489245124833722973 5471831433466921812646115)
        ·
          refine ⟨8207747150200382718969173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5471831433466921812646115 8207747150200382718969173)
          ·
            refine ⟨6011533557275670936745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8207747150200382718969173 6011533557275670936745)
            ·
              rfl

theorem cell23_2844903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 12].length) (baseStart_2844903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844903 prefixEnd_2844903 := by exact prefixLift 2844903
  have htrace : WordTrace (prefixWord ++ tailWord_2844903) baseStart_2844903 baseEnd_2844903 := by
    simpa [prefixWord, tailWord_2844903, baseEnd_2844903] using wordTrace_append hprefix tailTrace_2844903
  have hstable : (prefixWord ++ tailWord_2844903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844903).length < 2 ^ (prefixWord ++ tailWord_2844903).sum := by decide
  have hdescent : baseEnd_2844903 < baseStart_2844903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844963 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 4, 6]
def baseStart_2844963 : Nat := 118140960795 + 2844963 * 2 ^ 59
def prefixEnd_2844963 : Nat := 4983230072969 + 3 ^ 40 * 2844963 * 2
def baseEnd_2844963 : Nat := 486944487752419267626253

theorem tailTrace_2844963 : CollatzResearch.WordTrace tailWord_2844963 prefixEnd_2844963 486944487752419267626253 := by
  unfold tailWord_2844963
  simp only [CollatzResearch.WordTrace]
  refine ⟨103764325192192406842547543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69176216794794937895031695 103764325192192406842547543)
  ·
    refine ⟨155646487788288610263821315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103764325192192406842547543 155646487788288610263821315)
    ·
      refine ⟨233469731682432915395731973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155646487788288610263821315 233469731682432915395731973)
      ·
        refine ⟨43775574690456171636699745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233469731682432915395731973 43775574690456171636699745)
        ·
          refine ⟨32831681017842128727524809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43775574690456171636699745 32831681017842128727524809)
          ·
            refine ⟨24623760763381596545643607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32831681017842128727524809 24623760763381596545643607)
            ·
              refine ⟨36935641145072394818465411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24623760763381596545643607 36935641145072394818465411)
              ·
                refine ⟨55403461717608592227698117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36935641145072394818465411 55403461717608592227698117)
                ·
                  refine ⟨10388149072051611042693397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55403461717608592227698117 10388149072051611042693397)
                  ·
                    refine ⟨486944487752419267626253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10388149072051611042693397 486944487752419267626253)
                    ·
                      rfl

theorem cell23_2844963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 6].length) (baseStart_2844963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844963 prefixEnd_2844963 := by exact prefixLift 2844963
  have htrace : WordTrace (prefixWord ++ tailWord_2844963) baseStart_2844963 baseEnd_2844963 := by
    simpa [prefixWord, tailWord_2844963, baseEnd_2844963] using wordTrace_append hprefix tailTrace_2844963
  have hstable : (prefixWord ++ tailWord_2844963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844963).length < 2 ^ (prefixWord ++ tailWord_2844963).sum := by decide
  have hdescent : baseEnd_2844963 < baseStart_2844963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2844964 : List Nat := [2, 3, 1, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_2844964 : Nat := 118140960795 + 2844964 * 2 ^ 59
def prefixEnd_2844964 : Nat := 4983230072969 + 3 ^ 40 * 2844964 * 2
def baseEnd_2844964 : Nat := 1460833976737912298966255

theorem tailTrace_2844964 : CollatzResearch.WordTrace tailWord_2844964 prefixEnd_2844964 1460833976737912298966255 := by
  unfold tailWord_2844964
  simp only [CollatzResearch.WordTrace]
  refine ⟨51882180832594392006666973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69176241110125856008889297 51882180832594392006666973)
  ·
    refine ⟨19455817812222897002500115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51882180832594392006666973 19455817812222897002500115)
    ·
      refine ⟨29183726718334345503750173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19455817812222897002500115 29183726718334345503750173)
      ·
        refine ⟨10943897519375379563906315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29183726718334345503750173 10943897519375379563906315)
        ·
          refine ⟨16415846279063069345859473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10943897519375379563906315 16415846279063069345859473)
          ·
            refine ⟨12311884709297302009394605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16415846279063069345859473 12311884709297302009394605)
            ·
              refine ⟨4616956765986488253522977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12311884709297302009394605 4616956765986488253522977)
              ·
                refine ⟨3462717574489866190142233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4616956765986488253522977 3462717574489866190142233)
                ·
                  refine ⟨2597038180867399642606675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3462717574489866190142233 2597038180867399642606675)
                  ·
                    refine ⟨3895557271301099463910013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2597038180867399642606675 3895557271301099463910013)
                    ·
                      refine ⟨1460833976737912298966255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3895557271301099463910013 1460833976737912298966255)
                      ·
                        rfl

theorem cell23_2844964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_2844964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2844964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2844964 prefixEnd_2844964 := by exact prefixLift 2844964
  have htrace : WordTrace (prefixWord ++ tailWord_2844964) baseStart_2844964 baseEnd_2844964 := by
    simpa [prefixWord, tailWord_2844964, baseEnd_2844964] using wordTrace_append hprefix tailTrace_2844964
  have hstable : (prefixWord ++ tailWord_2844964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2844964).length < 2 ^ (prefixWord ++ tailWord_2844964).sum := by decide
  have hdescent : baseEnd_2844964 < baseStart_2844964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2844964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845057 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 2, 5]
def baseStart_2845057 : Nat := 118140960795 + 2845057 * 2 ^ 59
def prefixEnd_2845057 : Nat := 4983230072969 + 3 ^ 40 * 2845057 * 2
def baseEnd_2845057 : Nat := 486960576812926811701109

theorem tailTrace_2845057 : CollatzResearch.WordTrace tailWord_2845057 prefixEnd_2845057 486960576812926811701109 := by
  unfold tailWord_2845057
  simp only [CollatzResearch.WordTrace]
  refine ⟨103767753653851860896469425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69178502435901240597646283 103767753653851860896469425)
  ·
    refine ⟨77825815240388895672352069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103767753653851860896469425 77825815240388895672352069)
    ·
      refine ⟨14592340357572917938566013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77825815240388895672352069 14592340357572917938566013)
      ·
        refine ⟨5472127634089844226962255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14592340357572917938566013 5472127634089844226962255)
        ·
          refine ⟨8208191451134766340443383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5472127634089844226962255 8208191451134766340443383)
          ·
            refine ⟨12312287176702149510665075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8208191451134766340443383 12312287176702149510665075)
            ·
              refine ⟨18468430765053224265997613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12312287176702149510665075 18468430765053224265997613)
              ·
                refine ⟨6925661536894959099749105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18468430765053224265997613 6925661536894959099749105)
                ·
                  refine ⟨5194246152671219324811829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6925661536894959099749105 5194246152671219324811829)
                  ·
                    refine ⟨486960576812926811701109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5194246152671219324811829 486960576812926811701109)
                    ·
                      rfl

theorem cell23_2845057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_2845057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845057 prefixEnd_2845057 := by exact prefixLift 2845057
  have htrace : WordTrace (prefixWord ++ tailWord_2845057) baseStart_2845057 baseEnd_2845057 := by
    simpa [prefixWord, tailWord_2845057, baseEnd_2845057] using wordTrace_append hprefix tailTrace_2845057
  have hstable : (prefixWord ++ tailWord_2845057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845057).length < 2 ^ (prefixWord ++ tailWord_2845057).sum := by decide
  have hdescent : baseEnd_2845057 < baseStart_2845057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845077 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 2, 4, 2]
def baseStart_2845077 : Nat := 118140960795 + 2845077 * 2 ^ 59
def prefixEnd_2845077 : Nat := 4983230072969 + 3 ^ 40 * 2845077 * 2
def baseEnd_2845077 : Nat := 1460892000051870356853235

theorem tailTrace_2845077 : CollatzResearch.WordTrace tailWord_2845077 prefixEnd_2845077 1460892000051870356853235 := by
  unfold tailWord_2845077
  simp only [CollatzResearch.WordTrace]
  refine ⟨103768483113779404312197485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69178988742519602874798323 103768483113779404312197485)
  ·
    refine ⟨38913181167667276617074057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103768483113779404312197485 38913181167667276617074057)
    ·
      refine ⟨29184885875750457462805543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38913181167667276617074057 29184885875750457462805543)
      ·
        refine ⟨43777328813625686194208315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29184885875750457462805543 43777328813625686194208315)
        ·
          refine ⟨65665993220438529291312473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43777328813625686194208315 65665993220438529291312473)
          ·
            refine ⟨49249494915328896968484355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65665993220438529291312473 49249494915328896968484355)
            ·
              refine ⟨73874242372993345452726533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49249494915328896968484355 73874242372993345452726533)
              ·
                refine ⟨13851420444936252272386225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73874242372993345452726533 13851420444936252272386225)
                ·
                  refine ⟨10388565333702189204289669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13851420444936252272386225 10388565333702189204289669)
                  ·
                    refine ⟨1947856000069160475804313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10388565333702189204289669 1947856000069160475804313)
                    ·
                      refine ⟨1460892000051870356853235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1947856000069160475804313 1460892000051870356853235)
                      ·
                        rfl

theorem cell23_2845077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_2845077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845077 prefixEnd_2845077 := by exact prefixLift 2845077
  have htrace : WordTrace (prefixWord ++ tailWord_2845077) baseStart_2845077 baseEnd_2845077 := by
    simpa [prefixWord, tailWord_2845077, baseEnd_2845077] using wordTrace_append hprefix tailTrace_2845077
  have hstable : (prefixWord ++ tailWord_2845077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845077).length < 2 ^ (prefixWord ++ tailWord_2845077).sum := by decide
  have hdescent : baseEnd_2845077 < baseStart_2845077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
