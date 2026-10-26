import V185TrunkScan21Chunk053

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_652786 : List Nat := [3, 2, 1, 4, 1, 1, 3, 6]
def baseStart_652786 : Nat := 118140960795 + 652786 * 2 ^ 59
def prefixEnd_652786 : Nat := 4983230072969 + 3 ^ 40 * 652786 * 2
def baseEnd_652786 : Nat := 49658219633479734144133

theorem tailTrace_652786 : CollatzResearch.WordTrace tailWord_652786 prefixEnd_652786 49658219633479734144133 := by
  unfold tailWord_652786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5952265353268820954494553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15872707608716855878652141 5952265353268820954494553)
  ·
    refine ⟨4464199014951615715870915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5952265353268820954494553 4464199014951615715870915)
    ·
      refine ⟨6696298522427423573806373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4464199014951615715870915 6696298522427423573806373)
      ·
        refine ⟨1255555972955141920088695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6696298522427423573806373 1255555972955141920088695)
        ·
          refine ⟨1883333959432712880133043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255555972955141920088695 1883333959432712880133043)
          ·
            refine ⟨2825000939149069320199565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883333959432712880133043 2825000939149069320199565)
            ·
              refine ⟨1059375352180900995074837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2825000939149069320199565 1059375352180900995074837)
              ·
                refine ⟨49658219633479734144133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1059375352180900995074837 49658219633479734144133)
                ·
                  rfl

theorem cell21_652786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_652786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652786 prefixEnd_652786 := by exact prefixLift 652786
  have htrace : WordTrace (prefixWord ++ tailWord_652786) baseStart_652786 baseEnd_652786 := by
    simpa [prefixWord, tailWord_652786, baseEnd_652786] using wordTrace_append hprefix tailTrace_652786
  have hstable : (prefixWord ++ tailWord_652786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652786).length < 2 ^ (prefixWord ++ tailWord_652786).sum := by decide
  have hdescent : baseEnd_652786 < baseStart_652786 := by decide
  rcases family_descends (prefixWord ++ tailWord_652786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652817 : List Nat := [1, 2, 2, 1, 1, 2, 6, 3, 3]
def baseStart_652817 : Nat := 118140960795 + 652817 * 2 ^ 59
def prefixEnd_652817 : Nat := 4983230072969 + 3 ^ 40 * 652817 * 2
def baseEnd_652817 : Nat := 148981733522790037415669

theorem tailTrace_652817 : CollatzResearch.WordTrace tailWord_652817 prefixEnd_652817 148981733522790037415669 := by
  unfold tailWord_652817
  simp only [CollatzResearch.WordTrace]
  refine ⟨23810192075962976112356705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15873461383975317408237803 23810192075962976112356705)
  ·
    refine ⟨17857644056972232084267529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23810192075962976112356705 17857644056972232084267529)
    ·
      refine ⟨13393233042729174063200647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17857644056972232084267529 13393233042729174063200647)
      ·
        refine ⟨20089849564093761094800971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13393233042729174063200647 20089849564093761094800971)
        ·
          refine ⟨30134774346140641642201457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20089849564093761094800971 30134774346140641642201457)
          ·
            refine ⟨22601080759605481231651093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30134774346140641642201457 22601080759605481231651093)
            ·
              refine ⟨1059425660606506932733645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22601080759605481231651093 1059425660606506932733645)
              ·
                refine ⟨397284622727440099775117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1059425660606506932733645 397284622727440099775117)
                ·
                  refine ⟨148981733522790037415669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397284622727440099775117 148981733522790037415669)
                  ·
                    rfl

theorem cell21_652817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 3].length) (baseStart_652817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652817 prefixEnd_652817 := by exact prefixLift 652817
  have htrace : WordTrace (prefixWord ++ tailWord_652817) baseStart_652817 baseEnd_652817 := by
    simpa [prefixWord, tailWord_652817, baseEnd_652817] using wordTrace_append hprefix tailTrace_652817
  have hstable : (prefixWord ++ tailWord_652817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652817).length < 2 ^ (prefixWord ++ tailWord_652817).sum := by decide
  have hdescent : baseEnd_652817 < baseStart_652817 := by decide
  rcases family_descends (prefixWord ++ tailWord_652817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652831 : List Nat := [1, 1, 2, 4, 1, 1, 5, 2, 4]
def baseStart_652831 : Nat := 118140960795 + 652831 * 2 ^ 59
def prefixEnd_652831 : Nat := 4983230072969 + 3 ^ 40 * 652831 * 2
def baseEnd_652831 : Nat := 148984928513529124182307

theorem tailTrace_652831 : CollatzResearch.WordTrace tailWord_652831 prefixEnd_652831 148984928513529124182307 := by
  unfold tailWord_652831
  simp only [CollatzResearch.WordTrace]
  refine ⟨23810702697912256503366347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15873801798608171002244231 23810702697912256503366347)
  ·
    refine ⟨35716054046868384755049521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23810702697912256503366347 35716054046868384755049521)
    ·
      refine ⟨26787040535151288566287141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35716054046868384755049521 26787040535151288566287141)
      ·
        refine ⟨5022570100340866606178839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26787040535151288566287141 5022570100340866606178839)
        ·
          refine ⟨7533855150511299909268259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5022570100340866606178839 7533855150511299909268259)
          ·
            refine ⟨11300782725766949863902389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7533855150511299909268259 11300782725766949863902389)
            ·
              refine ⟨1059448380540651549740849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11300782725766949863902389 1059448380540651549740849)
              ·
                refine ⟨794586285405488662305637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1059448380540651549740849 794586285405488662305637)
                ·
                  refine ⟨148984928513529124182307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 794586285405488662305637 148984928513529124182307)
                  ·
                    rfl

theorem cell21_652831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 4].length) (baseStart_652831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652831 prefixEnd_652831 := by exact prefixLift 652831
  have htrace : WordTrace (prefixWord ++ tailWord_652831) baseStart_652831 baseEnd_652831 := by
    simpa [prefixWord, tailWord_652831, baseEnd_652831] using wordTrace_append hprefix tailTrace_652831
  have hstable : (prefixWord ++ tailWord_652831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652831).length < 2 ^ (prefixWord ++ tailWord_652831).sum := by decide
  have hdescent : baseEnd_652831 < baseStart_652831 := by decide
  rcases family_descends (prefixWord ++ tailWord_652831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653042 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_653042 : Nat := 118140960795 + 653042 * 2 ^ 59
def prefixEnd_653042 : Nat := 4983230072969 + 3 ^ 40 * 653042 * 2
def baseEnd_653042 : Nat := 149033081588239646165209

theorem tailTrace_653042 : CollatzResearch.WordTrace tailWord_653042 prefixEnd_653042 149033081588239646165209 := by
  unfold tailWord_653042
  simp only [CollatzResearch.WordTrace]
  refine ⟨5954599625036959884824345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15878932333431893026198253 5954599625036959884824345)
  ·
    refine ⟨4465949718777719913618259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5954599625036959884824345 4465949718777719913618259)
    ·
      refine ⟨6698924578166579870427389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4465949718777719913618259 6698924578166579870427389)
      ·
        refine ⟨2512096716812467451410271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6698924578166579870427389 2512096716812467451410271)
        ·
          refine ⟨3768145075218701177115407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2512096716812467451410271 3768145075218701177115407)
          ·
            refine ⟨5652217612828051765673111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3768145075218701177115407 5652217612828051765673111)
            ·
              refine ⟨8478326419242077648509667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5652217612828051765673111 8478326419242077648509667)
              ·
                refine ⟨12717489628863116472764501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8478326419242077648509667 12717489628863116472764501)
                ·
                  refine ⟨149033081588239646165209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12717489628863116472764501 149033081588239646165209)
                  ·
                    rfl

theorem cell21_653042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_653042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653042 prefixEnd_653042 := by exact prefixLift 653042
  have htrace : WordTrace (prefixWord ++ tailWord_653042) baseStart_653042 baseEnd_653042 := by
    simpa [prefixWord, tailWord_653042, baseEnd_653042] using wordTrace_append hprefix tailTrace_653042
  have hstable : (prefixWord ++ tailWord_653042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653042).length < 2 ^ (prefixWord ++ tailWord_653042).sum := by decide
  have hdescent : baseEnd_653042 < baseStart_653042 := by decide
  rcases family_descends (prefixWord ++ tailWord_653042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653087 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 7]
def baseStart_653087 : Nat := 118140960795 + 653087 * 2 ^ 59
def prefixEnd_653087 : Nat := 4983230072969 + 3 ^ 40 * 653087 * 2
def baseEnd_653087 : Nat := 149043351201329567915117

theorem tailTrace_653087 : CollatzResearch.WordTrace tailWord_653087 prefixEnd_653087 149043351201329567915117 := by
  unfold tailWord_653087
  simp only [CollatzResearch.WordTrace]
  refine ⟨23820039784984812224685515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15880026523323208149790343 23820039784984812224685515)
  ·
    refine ⟨35730059677477218337028273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23820039784984812224685515 35730059677477218337028273)
    ·
      refine ⟨26797544758107913752771205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35730059677477218337028273 26797544758107913752771205)
      ·
        refine ⟨5024539642145233828644601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26797544758107913752771205 5024539642145233828644601)
        ·
          refine ⟨3768404731608925371483451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5024539642145233828644601 3768404731608925371483451)
          ·
            refine ⟨5652607097413388057225177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3768404731608925371483451 5652607097413388057225177)
            ·
              refine ⟨4239455323060041042918883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5652607097413388057225177 4239455323060041042918883)
              ·
                refine ⟨6359182984590061564378325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4239455323060041042918883 6359182984590061564378325)
                ·
                  refine ⟨149043351201329567915117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6359182984590061564378325 149043351201329567915117)
                  ·
                    rfl

theorem cell21_653087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_653087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653087 prefixEnd_653087 := by exact prefixLift 653087
  have htrace : WordTrace (prefixWord ++ tailWord_653087) baseStart_653087 baseEnd_653087 := by
    simpa [prefixWord, tailWord_653087, baseEnd_653087] using wordTrace_append hprefix tailTrace_653087
  have hstable : (prefixWord ++ tailWord_653087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653087).length < 2 ^ (prefixWord ++ tailWord_653087).sum := by decide
  have hdescent : baseEnd_653087 < baseStart_653087 := by decide
  rcases family_descends (prefixWord ++ tailWord_653087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653253 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 8]
def baseStart_653253 : Nat := 118140960795 + 653253 * 2 ^ 59
def prefixEnd_653253 : Nat := 4983230072969 + 3 ^ 40 * 653253 * 2
def baseEnd_653253 : Nat := 149081234662950168148111

theorem tailTrace_653253 : CollatzResearch.WordTrace tailWord_653253 prefixEnd_653253 149081234662950168148111 := by
  unfold tailWord_653253
  simp only [CollatzResearch.WordTrace]
  refine ⟨23826094302383422575228413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15884062868255615050152275 23826094302383422575228413)
  ·
    refine ⟨8934785363393783465710655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23826094302383422575228413 8934785363393783465710655)
    ·
      refine ⟨13402178045090675198565983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8934785363393783465710655 13402178045090675198565983)
      ·
        refine ⟨20103267067636012797848975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13402178045090675198565983 20103267067636012797848975)
        ·
          refine ⟨30154900601454019196773463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20103267067636012797848975 30154900601454019196773463)
          ·
            refine ⟨45232350902181028795160195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30154900601454019196773463 45232350902181028795160195)
            ·
              refine ⟨67848526353271543192740293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45232350902181028795160195 67848526353271543192740293)
              ·
                refine ⟨12721598691238414348638805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67848526353271543192740293 12721598691238414348638805)
                ·
                  refine ⟨149081234662950168148111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12721598691238414348638805 149081234662950168148111)
                  ·
                    rfl

theorem cell21_653253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_653253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653253 prefixEnd_653253 := by exact prefixLift 653253
  have htrace : WordTrace (prefixWord ++ tailWord_653253) baseStart_653253 baseEnd_653253 := by
    simpa [prefixWord, tailWord_653253, baseEnd_653253] using wordTrace_append hprefix tailTrace_653253
  have hstable : (prefixWord ++ tailWord_653253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653253).length < 2 ^ (prefixWord ++ tailWord_653253).sum := by decide
  have hdescent : baseEnd_653253 < baseStart_653253 := by decide
  rcases family_descends (prefixWord ++ tailWord_653253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653346 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_653346 : Nat := 118140960795 + 653346 * 2 ^ 59
def prefixEnd_653346 : Nat := 4983230072969 + 3 ^ 40 * 653346 * 2
def baseEnd_653346 : Nat := 149102458530002673097921

theorem tailTrace_653346 : CollatzResearch.WordTrace tailWord_653346 prefixEnd_653346 149102458530002673097921 := by
  unfold tailWord_653346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5957371572761624864590973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15886324194030999638909261 5957371572761624864590973)
  ·
    refine ⟨2234014339785609324221615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5957371572761624864590973 2234014339785609324221615)
    ·
      refine ⟨3351021509678413986332423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2234014339785609324221615 3351021509678413986332423)
      ·
        refine ⟨5026532264517620979498635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3351021509678413986332423 5026532264517620979498635)
        ·
          refine ⟨7539798396776431469247953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026532264517620979498635 7539798396776431469247953)
          ·
            refine ⟨5654848797582323601935965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7539798396776431469247953 5654848797582323601935965)
            ·
              refine ⟨2120568299093371350725987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5654848797582323601935965 2120568299093371350725987)
              ·
                refine ⟨3180852448640057026088981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120568299093371350725987 3180852448640057026088981)
                ·
                  refine ⟨149102458530002673097921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3180852448640057026088981 149102458530002673097921)
                  ·
                    rfl

theorem cell21_653346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_653346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653346 prefixEnd_653346 := by exact prefixLift 653346
  have htrace : WordTrace (prefixWord ++ tailWord_653346) baseStart_653346 baseEnd_653346 := by
    simpa [prefixWord, tailWord_653346, baseEnd_653346] using wordTrace_append hprefix tailTrace_653346
  have hstable : (prefixWord ++ tailWord_653346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653346).length < 2 ^ (prefixWord ++ tailWord_653346).sum := by decide
  have hdescent : baseEnd_653346 < baseStart_653346 := by decide
  rcases family_descends (prefixWord ++ tailWord_653346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653377 : List Nat := [1, 2, 5, 1, 2, 2, 1, 7]
def baseStart_653377 : Nat := 118140960795 + 653377 * 2 ^ 59
def prefixEnd_653377 : Nat := 4983230072969 + 3 ^ 40 * 653377 * 2
def baseEnd_653377 : Nat := 49703177717451169360397

theorem tailTrace_653377 : CollatzResearch.WordTrace tailWord_653377 prefixEnd_653377 49703177717451169360397 := by
  unfold tailWord_653377
  simp only [CollatzResearch.WordTrace]
  refine ⟨23830616953934191752742385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15887077969289461168494923 23830616953934191752742385)
  ·
    refine ⟨17872962715450643814556789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23830616953934191752742385 17872962715450643814556789)
    ·
      refine ⟨1675590254573497857614699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17872962715450643814556789 1675590254573497857614699)
      ·
        refine ⟨2513385381860246786422049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1675590254573497857614699 2513385381860246786422049)
        ·
          refine ⟨1885039036395185089816537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2513385381860246786422049 1885039036395185089816537)
          ·
            refine ⟨1413779277296388817362403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1885039036395185089816537 1413779277296388817362403)
            ·
              refine ⟨2120668915944583226043605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1413779277296388817362403 2120668915944583226043605)
              ·
                refine ⟨49703177717451169360397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2120668915944583226043605 49703177717451169360397)
                ·
                  rfl

theorem cell21_653377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 7].length) (baseStart_653377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653377 prefixEnd_653377 := by exact prefixLift 653377
  have htrace : WordTrace (prefixWord ++ tailWord_653377) baseStart_653377 baseEnd_653377 := by
    simpa [prefixWord, tailWord_653377, baseEnd_653377] using wordTrace_append hprefix tailTrace_653377
  have hstable : (prefixWord ++ tailWord_653377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653377).length < 2 ^ (prefixWord ++ tailWord_653377).sum := by decide
  have hdescent : baseEnd_653377 < baseStart_653377 := by decide
  rcases family_descends (prefixWord ++ tailWord_653377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653394 : List Nat := [3, 2, 2, 1, 5, 1, 7]
def baseStart_653394 : Nat := 118140960795 + 653394 * 2 ^ 59
def prefixEnd_653394 : Nat := 4983230072969 + 3 ^ 40 * 653394 * 2
def baseEnd_653394 : Nat := 16568156975996139588647

theorem tailTrace_653394 : CollatzResearch.WordTrace tailWord_653394 prefixEnd_653394 16568156975996139588647 := by
  unfold tailWord_653394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5957809248718150914027809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15887491329915069104074157 5957809248718150914027809)
  ·
    refine ⟨4468356936538613185520857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5957809248718150914027809 4468356936538613185520857)
    ·
      refine ⟨3351267702403959889140643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4468356936538613185520857 3351267702403959889140643)
      ·
        refine ⟨5026901553605939833710965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3351267702403959889140643 5026901553605939833710965)
        ·
          refine ⟨471272020650556859410403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5026901553605939833710965 471272020650556859410403)
          ·
            refine ⟨706908030975835289115605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471272020650556859410403 706908030975835289115605)
            ·
              refine ⟨16568156975996139588647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 706908030975835289115605 16568156975996139588647)
              ·
                rfl

theorem cell21_653394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 7].length) (baseStart_653394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653394 prefixEnd_653394 := by exact prefixLift 653394
  have htrace : WordTrace (prefixWord ++ tailWord_653394) baseStart_653394 baseEnd_653394 := by
    simpa [prefixWord, tailWord_653394, baseEnd_653394] using wordTrace_append hprefix tailTrace_653394
  have hstable : (prefixWord ++ tailWord_653394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653394).length < 2 ^ (prefixWord ++ tailWord_653394).sum := by decide
  have hdescent : baseEnd_653394 < baseStart_653394 := by decide
  rcases family_descends (prefixWord ++ tailWord_653394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653408 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 5]
def baseStart_653408 : Nat := 118140960795 + 653408 * 2 ^ 59
def prefixEnd_653408 : Nat := 4983230072969 + 3 ^ 40 * 653408 * 2
def baseEnd_653408 : Nat := 149116607774704343064461

theorem tailTrace_653408 : CollatzResearch.WordTrace tailWord_653408 prefixEnd_653408 149116607774704343064461 := by
  unfold tailWord_653408
  simp only [CollatzResearch.WordTrace]
  refine ⟨11915873808410942023560439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15887831744547922698080585 11915873808410942023560439)
  ·
    refine ⟨17873810712616413035340659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11915873808410942023560439 17873810712616413035340659)
    ·
      refine ⟨26810716068924619553010989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17873810712616413035340659 26810716068924619553010989)
      ·
        refine ⟨10054018525846732332379121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26810716068924619553010989 10054018525846732332379121)
        ·
          refine ⟨7540513894385049249284341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10054018525846732332379121 7540513894385049249284341)
          ·
            refine ⟨706923177598598367120407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7540513894385049249284341 706923177598598367120407)
            ·
              refine ⟨1060384766397897550680611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706923177598598367120407 1060384766397897550680611)
              ·
                refine ⟨1590577149596846326020917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060384766397897550680611 1590577149596846326020917)
                ·
                  refine ⟨149116607774704343064461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1590577149596846326020917 149116607774704343064461)
                  ·
                    rfl

theorem cell21_653408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_653408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653408 prefixEnd_653408 := by exact prefixLift 653408
  have htrace : WordTrace (prefixWord ++ tailWord_653408) baseStart_653408 baseEnd_653408 := by
    simpa [prefixWord, tailWord_653408, baseEnd_653408] using wordTrace_append hprefix tailTrace_653408
  have hstable : (prefixWord ++ tailWord_653408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653408).length < 2 ^ (prefixWord ++ tailWord_653408).sum := by decide
  have hdescent : baseEnd_653408 < baseStart_653408 := by decide
  rcases family_descends (prefixWord ++ tailWord_653408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653436 : List Nat := [2, 2, 2, 1, 1, 4, 2, 7]
def baseStart_653436 : Nat := 118140960795 + 653436 * 2 ^ 59
def prefixEnd_653436 : Nat := 4983230072969 + 3 ^ 40 * 653436 * 2
def baseEnd_653436 : Nat := 49707665918727505532579

theorem tailTrace_653436 : CollatzResearch.WordTrace tailWord_653436 prefixEnd_653436 49707665918727505532579 := by
  unfold tailWord_653436
  simp only [CollatzResearch.WordTrace]
  refine ⟨11916384430360222414570081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15888512573813629886093441 11916384430360222414570081)
  ·
    refine ⟨8937288322770166810927561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11916384430360222414570081 8937288322770166810927561)
    ·
      refine ⟨6702966242077625108195671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8937288322770166810927561 6702966242077625108195671)
      ·
        refine ⟨10054449363116437662293507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6702966242077625108195671 10054449363116437662293507)
        ·
          refine ⟨15081674044674656493440261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10054449363116437662293507 15081674044674656493440261)
          ·
            refine ⟨2827813883376498092520049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15081674044674656493440261 2827813883376498092520049)
            ·
              refine ⟨2120860412532373569390037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2827813883376498092520049 2120860412532373569390037)
              ·
                refine ⟨49707665918727505532579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2120860412532373569390037 49707665918727505532579)
                ·
                  rfl

theorem cell21_653436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_653436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653436 prefixEnd_653436 := by exact prefixLift 653436
  have htrace : WordTrace (prefixWord ++ tailWord_653436) baseStart_653436 baseEnd_653436 := by
    simpa [prefixWord, tailWord_653436, baseEnd_653436] using wordTrace_append hprefix tailTrace_653436
  have hstable : (prefixWord ++ tailWord_653436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653436).length < 2 ^ (prefixWord ++ tailWord_653436).sum := by decide
  have hdescent : baseEnd_653436 < baseStart_653436 := by decide
  rcases family_descends (prefixWord ++ tailWord_653436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653462 : List Nat := [5, 3, 2, 1, 2, 1, 1, 6]
def baseStart_653462 : Nat := 118140960795 + 653462 * 2 ^ 59
def prefixEnd_653462 : Nat := 4983230072969 + 3 ^ 40 * 653462 * 2
def baseEnd_653462 : Nat := 49709643770137416388117

theorem tailTrace_653462 : CollatzResearch.WordTrace tailWord_653462 prefixEnd_653462 49709643770137416388117 := by
  unfold tailWord_653462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1489607322414140704349165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15889144772417500846391093 1489607322414140704349165)
  ·
    refine ⟨558602745905302764130937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1489607322414140704349165 558602745905302764130937)
    ·
      refine ⟨418952059428977073098203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 558602745905302764130937 418952059428977073098203)
      ·
        refine ⟨628428089143465609647305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418952059428977073098203 628428089143465609647305)
        ·
          refine ⟨471321066857599207235479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 628428089143465609647305 471321066857599207235479)
          ·
            refine ⟨706981600286398810853219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471321066857599207235479 706981600286398810853219)
            ·
              refine ⟨1060472400429598216279829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706981600286398810853219 1060472400429598216279829)
              ·
                refine ⟨49709643770137416388117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1060472400429598216279829 49709643770137416388117)
                ·
                  rfl

theorem cell21_653462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_653462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653462 prefixEnd_653462 := by exact prefixLift 653462
  have htrace : WordTrace (prefixWord ++ tailWord_653462) baseStart_653462 baseEnd_653462 := by
    simpa [prefixWord, tailWord_653462, baseEnd_653462] using wordTrace_append hprefix tailTrace_653462
  have hstable : (prefixWord ++ tailWord_653462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653462).length < 2 ^ (prefixWord ++ tailWord_653462).sum := by decide
  have hdescent : baseEnd_653462 < baseStart_653462 := by decide
  rcases family_descends (prefixWord ++ tailWord_653462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653577 : List Nat := [1, 2, 1, 1, 3, 5, 3, 2, 3]
def baseStart_653577 : Nat := 118140960795 + 653577 * 2 ^ 59
def prefixEnd_653577 : Nat := 4983230072969 + 3 ^ 40 * 653577 * 2
def baseEnd_653577 : Nat := 149155175877197604747449

theorem tailTrace_653577 : CollatzResearch.WordTrace tailWord_653577 prefixEnd_653577 149155175877197604747449 := by
  unfold tailWord_653577
  simp only [CollatzResearch.WordTrace]
  refine ⟨23837911553209625910022985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15891941035473083940015323 23837911553209625910022985)
  ·
    refine ⟨17878433664907219432517239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23837911553209625910022985 17878433664907219432517239)
    ·
      refine ⟨26817650497360829148775859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17878433664907219432517239 26817650497360829148775859)
      ·
        refine ⟨40226475746041243723163789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26817650497360829148775859 40226475746041243723163789)
        ·
          refine ⟨15084928404765466396186421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40226475746041243723163789 15084928404765466396186421)
          ·
            refine ⟨1414212037946762474642477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15084928404765466396186421 1414212037946762474642477)
            ·
              refine ⟨530329514230035927990929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1414212037946762474642477 530329514230035927990929)
              ·
                refine ⟨397747135672526945993197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 530329514230035927990929 397747135672526945993197)
                ·
                  refine ⟨149155175877197604747449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397747135672526945993197 149155175877197604747449)
                  ·
                    rfl

theorem cell21_653577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 3].length) (baseStart_653577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653577 prefixEnd_653577 := by exact prefixLift 653577
  have htrace : WordTrace (prefixWord ++ tailWord_653577) baseStart_653577 baseEnd_653577 := by
    simpa [prefixWord, tailWord_653577, baseEnd_653577] using wordTrace_append hprefix tailTrace_653577
  have hstable : (prefixWord ++ tailWord_653577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653577).length < 2 ^ (prefixWord ++ tailWord_653577).sum := by decide
  have hdescent : baseEnd_653577 < baseStart_653577 := by decide
  rcases family_descends (prefixWord ++ tailWord_653577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653591 : List Nat := [1, 1, 3, 4, 1, 2, 4, 1, 4]
def baseStart_653591 : Nat := 118140960795 + 653591 * 2 ^ 59
def prefixEnd_653591 : Nat := 4983230072969 + 3 ^ 40 * 653591 * 2
def baseEnd_653591 : Nat := 149158370867936691514087

theorem tailTrace_653591 : CollatzResearch.WordTrace tailWord_653591 prefixEnd_653591 149158370867936691514087 := by
  unfold tailWord_653591
  simp only [CollatzResearch.WordTrace]
  refine ⟨23838422175158906301032627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15892281450105937534021751 23838422175158906301032627)
  ·
    refine ⟨35757633262738359451548941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23838422175158906301032627 35757633262738359451548941)
    ·
      refine ⟨13409112473526884794330853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35757633262738359451548941 13409112473526884794330853)
      ·
        refine ⟨2514208588786290898937035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13409112473526884794330853 2514208588786290898937035)
        ·
          refine ⟨3771312883179436348405553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514208588786290898937035 3771312883179436348405553)
          ·
            refine ⟨2828484662384577261304165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3771312883179436348405553 2828484662384577261304165)
            ·
              refine ⟨530340874197108236494531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2828484662384577261304165 530340874197108236494531)
              ·
                refine ⟨795511311295662354741797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530340874197108236494531 795511311295662354741797)
                ·
                  refine ⟨149158370867936691514087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 795511311295662354741797 149158370867936691514087)
                  ·
                    rfl

theorem cell21_653591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 4].length) (baseStart_653591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653591 prefixEnd_653591 := by exact prefixLift 653591
  have htrace : WordTrace (prefixWord ++ tailWord_653591) baseStart_653591 baseEnd_653591 := by
    simpa [prefixWord, tailWord_653591, baseEnd_653591] using wordTrace_append hprefix tailTrace_653591
  have hstable : (prefixWord ++ tailWord_653591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653591).length < 2 ^ (prefixWord ++ tailWord_653591).sum := by decide
  have hdescent : baseEnd_653591 < baseStart_653591 := by decide
  rcases family_descends (prefixWord ++ tailWord_653591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653647 : List Nat := [1, 1, 2, 1, 1, 2, 1, 12]
def baseStart_653647 : Nat := 118140960795 + 653647 * 2 ^ 59
def prefixEnd_653647 : Nat := 4983230072969 + 3 ^ 40 * 653647 * 2
def baseEnd_653647 : Nat := 49723716943631012860213

theorem tailTrace_653647 : CollatzResearch.WordTrace tailWord_653647 prefixEnd_653647 49723716943631012860213 := by
  unfold tailWord_653647
  simp only [CollatzResearch.WordTrace]
  refine ⟨23840464662956027865071195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15893643108637351910047463 23840464662956027865071195)
  ·
    refine ⟨35760696994434041797606793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23840464662956027865071195 35760696994434041797606793)
    ·
      refine ⟨26820522745825531348205095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35760696994434041797606793 26820522745825531348205095)
      ·
        refine ⟨40230784118738297022307643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26820522745825531348205095 40230784118738297022307643)
        ·
          refine ⟨60346176178107445533461465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40230784118738297022307643 60346176178107445533461465)
          ·
            refine ⟨45259632133580584150096099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60346176178107445533461465 45259632133580584150096099)
            ·
              refine ⟨67889448200370876225144149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45259632133580584150096099 67889448200370876225144149)
              ·
                refine ⟨49723716943631012860213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 67889448200370876225144149 49723716943631012860213)
                ·
                  rfl

theorem cell21_653647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 12].length) (baseStart_653647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653647 prefixEnd_653647 := by exact prefixLift 653647
  have htrace : WordTrace (prefixWord ++ tailWord_653647) baseStart_653647 baseEnd_653647 := by
    simpa [prefixWord, tailWord_653647, baseEnd_653647] using wordTrace_append hprefix tailTrace_653647
  have hstable : (prefixWord ++ tailWord_653647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653647).length < 2 ^ (prefixWord ++ tailWord_653647).sum := by decide
  have hdescent : baseEnd_653647 < baseStart_653647 := by decide
  rcases family_descends (prefixWord ++ tailWord_653647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653650 : List Nat := [3, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_653650 : Nat := 118140960795 + 653650 * 2 ^ 59
def prefixEnd_653650 : Nat := 4983230072969 + 3 ^ 40 * 653650 * 2
def baseEnd_653650 : Nat := 149171835471765700030633

theorem tailTrace_653650 : CollatzResearch.WordTrace tailWord_653650 prefixEnd_653650 149171835471765700030633 := by
  unfold tailWord_653650
  simp only [CollatzResearch.WordTrace]
  refine ⟨5960143520486289844357601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15893716054630106251620269 5960143520486289844357601)
  ·
    refine ⟨4470107640364717383268201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5960143520486289844357601 4470107640364717383268201)
    ·
      refine ⟨3352580730273538037451151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4470107640364717383268201 3352580730273538037451151)
      ·
        refine ⟨5028871095410307056176727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3352580730273538037451151 5028871095410307056176727)
        ·
          refine ⟨7543306643115460584265091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5028871095410307056176727 7543306643115460584265091)
          ·
            refine ⟨11314959964673190876397637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7543306643115460584265091 11314959964673190876397637)
            ·
              refine ⟨2121554993376223289324557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11314959964673190876397637 2121554993376223289324557)
              ·
                refine ⟨795583122516083733496709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2121554993376223289324557 795583122516083733496709)
                ·
                  refine ⟨149171835471765700030633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 795583122516083733496709 149171835471765700030633)
                  ·
                    rfl

theorem cell21_653650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_653650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653650 prefixEnd_653650 := by exact prefixLift 653650
  have htrace : WordTrace (prefixWord ++ tailWord_653650) baseStart_653650 baseEnd_653650 := by
    simpa [prefixWord, tailWord_653650, baseEnd_653650] using wordTrace_append hprefix tailTrace_653650
  have hstable : (prefixWord ++ tailWord_653650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653650).length < 2 ^ (prefixWord ++ tailWord_653650).sum := by decide
  have hdescent : baseEnd_653650 < baseStart_653650 := by decide
  rcases family_descends (prefixWord ++ tailWord_653650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653802 : List Nat := [3, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_653802 : Nat := 118140960795 + 653802 * 2 ^ 59
def prefixEnd_653802 : Nat := 4983230072969 + 3 ^ 40 * 653802 * 2
def baseEnd_653802 : Nat := 149206523942647213496989

theorem tailTrace_653802 : CollatzResearch.WordTrace tailWord_653802 prefixEnd_653802 149206523942647213496989 := by
  unfold tailWord_653802
  simp only [CollatzResearch.WordTrace]
  refine ⟨5961529494348622334240915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15897411984929659557975773 5961529494348622334240915)
  ·
    refine ⟨8942294241522933501361373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5961529494348622334240915 8942294241522933501361373)
    ·
      refine ⟨3353360340571100063010515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8942294241522933501361373 3353360340571100063010515)
      ·
        refine ⟨5030040510856650094515773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3353360340571100063010515 5030040510856650094515773)
        ·
          refine ⟨1886265191571243785443415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5030040510856650094515773 1886265191571243785443415)
          ·
            refine ⟨2829397787356865678165123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886265191571243785443415 2829397787356865678165123)
            ·
              refine ⟨4244096681035298517247685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829397787356865678165123 4244096681035298517247685)
              ·
                refine ⟨795768127694118471983941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4244096681035298517247685 795768127694118471983941)
                ·
                  refine ⟨149206523942647213496989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 795768127694118471983941 149206523942647213496989)
                  ·
                    rfl

theorem cell21_653802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_653802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653802 prefixEnd_653802 := by exact prefixLift 653802
  have htrace : WordTrace (prefixWord ++ tailWord_653802) baseStart_653802 baseEnd_653802 := by
    simpa [prefixWord, tailWord_653802, baseEnd_653802] using wordTrace_append hprefix tailTrace_653802
  have hstable : (prefixWord ++ tailWord_653802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653802).length < 2 ^ (prefixWord ++ tailWord_653802).sum := by decide
  have hdescent : baseEnd_653802 < baseStart_653802 := by decide
  rcases family_descends (prefixWord ++ tailWord_653802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653805 : List Nat := [1, 5, 1, 3, 1, 2, 1, 4, 3]
def baseStart_653805 : Nat := 118140960795 + 653805 * 2 ^ 59
def prefixEnd_653805 : Nat := 4983230072969 + 3 ^ 40 * 653805 * 2
def baseEnd_653805 : Nat := 149207208583519874946983

theorem tailTrace_653805 : CollatzResearch.WordTrace tailWord_653805 prefixEnd_653805 149207208583519874946983 := by
  unfold tailWord_653805
  simp only [CollatzResearch.WordTrace]
  refine ⟨23846227396383620849322869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15897484930922413899548579 23846227396383620849322869)
  ·
    refine ⟨2235583818410964454624019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23846227396383620849322869 2235583818410964454624019)
    ·
      refine ⟨3353375727616446681936029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2235583818410964454624019 3353375727616446681936029)
      ·
        refine ⟨1257515897856167505726011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3353375727616446681936029 1257515897856167505726011)
        ·
          refine ⟨1886273846784251258589017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257515897856167505726011 1886273846784251258589017)
          ·
            refine ⟨1414705385088188443941763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1886273846784251258589017 1414705385088188443941763)
            ·
              refine ⟨2122058077632282665912645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414705385088188443941763 2122058077632282665912645)
              ·
                refine ⟨397885889556052999858621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2122058077632282665912645 397885889556052999858621)
                ·
                  refine ⟨149207208583519874946983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397885889556052999858621 149207208583519874946983)
                  ·
                    rfl

theorem cell21_653805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_653805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653805 prefixEnd_653805 := by exact prefixLift 653805
  have htrace : WordTrace (prefixWord ++ tailWord_653805) baseStart_653805 baseEnd_653805 := by
    simpa [prefixWord, tailWord_653805, baseEnd_653805] using wordTrace_append hprefix tailTrace_653805
  have hstable : (prefixWord ++ tailWord_653805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653805).length < 2 ^ (prefixWord ++ tailWord_653805).sum := by decide
  have hdescent : baseEnd_653805 < baseStart_653805 := by decide
  rcases family_descends (prefixWord ++ tailWord_653805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653864 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 5]
def baseStart_653864 : Nat := 118140960795 + 653864 * 2 ^ 59
def prefixEnd_653864 : Nat := 4983230072969 + 3 ^ 40 * 653864 * 2
def baseEnd_653864 : Nat := 149220673187348883463529

theorem tailTrace_653864 : CollatzResearch.WordTrace tailWord_653864 prefixEnd_653864 149220673187348883463529 := by
  unfold tailWord_653864
  simp only [CollatzResearch.WordTrace]
  refine ⟨11924189651584936962860323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15898919535446582617147097 11924189651584936962860323)
  ·
    refine ⟨17886284477377405444290485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11924189651584936962860323 17886284477377405444290485)
    ·
      refine ⟨1676839169754131760402233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17886284477377405444290485 1676839169754131760402233)
      ·
        refine ⟨1257629377315598820301675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1676839169754131760402233 1257629377315598820301675)
        ·
          refine ⟨1886444065973398230452513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257629377315598820301675 1886444065973398230452513)
          ·
            refine ⟨1414833049480048672839385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1886444065973398230452513 1414833049480048672839385)
            ·
              refine ⟨1061124787110036504629539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1414833049480048672839385 1061124787110036504629539)
              ·
                refine ⟨1591687180665054756944309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061124787110036504629539 1591687180665054756944309)
                ·
                  refine ⟨149220673187348883463529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1591687180665054756944309 149220673187348883463529)
                  ·
                    rfl

theorem cell21_653864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_653864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653864 prefixEnd_653864 := by exact prefixLift 653864
  have htrace : WordTrace (prefixWord ++ tailWord_653864) baseStart_653864 baseEnd_653864 := by
    simpa [prefixWord, tailWord_653864, baseEnd_653864] using wordTrace_append hprefix tailTrace_653864
  have hstable : (prefixWord ++ tailWord_653864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653864).length < 2 ^ (prefixWord ++ tailWord_653864).sum := by decide
  have hdescent : baseEnd_653864 < baseStart_653864 := by decide
  rcases family_descends (prefixWord ++ tailWord_653864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653875 : List Nat := [1, 1, 1, 2, 4, 2, 2, 8]
def baseStart_653875 : Nat := 118140960795 + 653875 * 2 ^ 59
def prefixEnd_653875 : Nat := 4983230072969 + 3 ^ 40 * 653875 * 2
def baseEnd_653875 : Nat := 49741061179071769593391

theorem tailTrace_653875 : CollatzResearch.WordTrace tailWord_653875 prefixEnd_653875 49741061179071769593391 := by
  unfold tailWord_653875
  simp only [CollatzResearch.WordTrace]
  refine ⟨23848780506130022804371079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15899187004086681869580719 23848780506130022804371079)
  ·
    refine ⟨35773170759195034206556619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23848780506130022804371079 35773170759195034206556619)
    ·
      refine ⟨53659756138792551309834929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35773170759195034206556619 53659756138792551309834929)
      ·
        refine ⟨40244817104094413482376197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53659756138792551309834929 40244817104094413482376197)
        ·
          refine ⟨7545903207017702527945537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40244817104094413482376197 7545903207017702527945537)
          ·
            refine ⟨5659427405263276895959153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7545903207017702527945537 5659427405263276895959153)
            ·
              refine ⟨4244570553947457671969365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5659427405263276895959153 4244570553947457671969365)
              ·
                refine ⟨49741061179071769593391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4244570553947457671969365 49741061179071769593391)
                ·
                  rfl

theorem cell21_653875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 8].length) (baseStart_653875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653875 prefixEnd_653875 := by exact prefixLift 653875
  have htrace : WordTrace (prefixWord ++ tailWord_653875) baseStart_653875 baseEnd_653875 := by
    simpa [prefixWord, tailWord_653875, baseEnd_653875] using wordTrace_append hprefix tailTrace_653875
  have hstable : (prefixWord ++ tailWord_653875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653875).length < 2 ^ (prefixWord ++ tailWord_653875).sum := by decide
  have hdescent : baseEnd_653875 < baseStart_653875 := by decide
  rcases family_descends (prefixWord ++ tailWord_653875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653985 : List Nat := [1, 2, 3, 3, 3, 2, 1, 6]
def baseStart_653985 : Nat := 118140960795 + 653985 * 2 ^ 59
def prefixEnd_653985 : Nat := 4983230072969 + 3 ^ 40 * 653985 * 2
def baseEnd_653985 : Nat := 49749429011959853982205

theorem tailTrace_653985 : CollatzResearch.WordTrace tailWord_653985 prefixEnd_653985 49749429011959853982205 := by
  unfold tailWord_653985
  simp only [CollatzResearch.WordTrace]
  refine ⟨23852792535731511590875409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15901861690487674393916939 23852792535731511590875409)
  ·
    refine ⟨17889594401798633693156557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23852792535731511590875409 17889594401798633693156557)
    ·
      refine ⟨6708597900674487634933709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17889594401798633693156557 6708597900674487634933709)
      ·
        refine ⟨2515724212752932863100141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6708597900674487634933709 2515724212752932863100141)
        ·
          refine ⟨943396579782349823662553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2515724212752932863100141 943396579782349823662553)
          ·
            refine ⟨707547434836762367746915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 943396579782349823662553 707547434836762367746915)
            ·
              refine ⟨1061321152255143551620373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707547434836762367746915 1061321152255143551620373)
              ·
                refine ⟨49749429011959853982205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1061321152255143551620373 49749429011959853982205)
                ·
                  rfl

theorem cell21_653985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 6].length) (baseStart_653985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_653985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_653985 prefixEnd_653985 := by exact prefixLift 653985
  have htrace : WordTrace (prefixWord ++ tailWord_653985) baseStart_653985 baseEnd_653985 := by
    simpa [prefixWord, tailWord_653985, baseEnd_653985] using wordTrace_append hprefix tailTrace_653985
  have hstable : (prefixWord ++ tailWord_653985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653985).length < 2 ^ (prefixWord ++ tailWord_653985).sum := by decide
  have hdescent : baseEnd_653985 < baseStart_653985 := by decide
  rcases family_descends (prefixWord ++ tailWord_653985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654016 : List Nat := [2, 1, 1, 2, 4, 3, 2, 3, 3]
def baseStart_654016 : Nat := 118140960795 + 654016 * 2 ^ 59
def prefixEnd_654016 : Nat := 4983230072969 + 3 ^ 40 * 654016 * 2
def baseEnd_654016 : Nat := 149255361658230396929885

theorem tailTrace_654016 : CollatzResearch.WordTrace tailWord_654016 prefixEnd_654016 149255361658230396929885 := by
  unfold tailWord_654016
  simp only [CollatzResearch.WordTrace]
  refine ⟨11926961599309601942626951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15902615465746135923502601 11926961599309601942626951)
  ·
    refine ⟨17890442398964402913940427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11926961599309601942626951 17890442398964402913940427)
    ·
      refine ⟨26835663598446604370910641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17890442398964402913940427 26835663598446604370910641)
      ·
        refine ⟨20126747698834953278182981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26835663598446604370910641 20126747698834953278182981)
        ·
          refine ⟨3773765193531553739659309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20126747698834953278182981 3773765193531553739659309)
          ·
            refine ⟨1415161947574332652372241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3773765193531553739659309 1415161947574332652372241)
            ·
              refine ⟨1061371460680749489279181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1415161947574332652372241 1061371460680749489279181)
              ·
                refine ⟨398014297755281058479693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1061371460680749489279181 398014297755281058479693)
                ·
                  refine ⟨149255361658230396929885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398014297755281058479693 149255361658230396929885)
                  ·
                    rfl

theorem cell21_654016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 3].length) (baseStart_654016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654016 prefixEnd_654016 := by exact prefixLift 654016
  have htrace : WordTrace (prefixWord ++ tailWord_654016) baseStart_654016 baseEnd_654016 := by
    simpa [prefixWord, tailWord_654016, baseEnd_654016] using wordTrace_append hprefix tailTrace_654016
  have hstable : (prefixWord ++ tailWord_654016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654016).length < 2 ^ (prefixWord ++ tailWord_654016).sum := by decide
  have hdescent : baseEnd_654016 < baseStart_654016 := by decide
  rcases family_descends (prefixWord ++ tailWord_654016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654022 : List Nat := [6, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_654022 : Nat := 118140960795 + 654022 * 2 ^ 59
def prefixEnd_654022 : Nat := 4983230072969 + 3 ^ 40 * 654022 * 2
def baseEnd_654022 : Nat := 149256730939975719829873

theorem tailTrace_654022 : CollatzResearch.WordTrace tailWord_654022 prefixEnd_654022 149256730939975719829873 := by
  unfold tailWord_654022
  simp only [CollatzResearch.WordTrace]
  refine ⟨745441938643670840936635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15902761357731644606648213 745441938643670840936635)
  ·
    refine ⟨1118162907965506261404953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 745441938643670840936635 1118162907965506261404953)
    ·
      refine ⟨838622180974129696053715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1118162907965506261404953 838622180974129696053715)
      ·
        refine ⟨1257933271461194544080573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 838622180974129696053715 1257933271461194544080573)
        ·
          refine ⟨471724976797947954030215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1257933271461194544080573 471724976797947954030215)
          ·
            refine ⟨707587465196921931045323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471724976797947954030215 707587465196921931045323)
            ·
              refine ⟨1061381197795382896567985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707587465196921931045323 1061381197795382896567985)
              ·
                refine ⟨796035898346537172425989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061381197795382896567985 796035898346537172425989)
                ·
                  refine ⟨149256730939975719829873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 796035898346537172425989 149256730939975719829873)
                  ·
                    rfl

theorem cell21_654022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_654022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654022 prefixEnd_654022 := by exact prefixLift 654022
  have htrace : WordTrace (prefixWord ++ tailWord_654022) baseStart_654022 baseEnd_654022 := by
    simpa [prefixWord, tailWord_654022, baseEnd_654022] using wordTrace_append hprefix tailTrace_654022
  have hstable : (prefixWord ++ tailWord_654022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654022).length < 2 ^ (prefixWord ++ tailWord_654022).sum := by decide
  have hdescent : baseEnd_654022 < baseStart_654022 := by decide
  rcases family_descends (prefixWord ++ tailWord_654022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654030 : List Nat := [4, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_654030 : Nat := 118140960795 + 654030 * 2 ^ 59
def prefixEnd_654030 : Nat := 4983230072969 + 3 ^ 40 * 654030 * 2
def baseEnd_654030 : Nat := 149258556648969483696523

theorem tailTrace_654030 : CollatzResearch.WordTrace tailWord_654030 prefixEnd_654030 149258556648969483696523 := by
  unfold tailWord_654030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2981804227571060534532943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15902955880378989517509029 2981804227571060534532943)
  ·
    refine ⟨4472706341356590801799415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2981804227571060534532943 4472706341356590801799415)
    ·
      refine ⟨6709059512034886202699123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4472706341356590801799415 6709059512034886202699123)
      ·
        refine ⟨10063589268052329304048685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6709059512034886202699123 10063589268052329304048685)
        ·
          refine ⟨3773845975519623489018257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10063589268052329304048685 3773845975519623489018257)
          ·
            refine ⟨2830384481639717616763693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3773845975519623489018257 2830384481639717616763693)
            ·
              refine ⟨1061394180614894106286385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2830384481639717616763693 1061394180614894106286385)
              ·
                refine ⟨796045635461170579714789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061394180614894106286385 796045635461170579714789)
                ·
                  refine ⟨149258556648969483696523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 796045635461170579714789 149258556648969483696523)
                  ·
                    rfl

theorem cell21_654030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_654030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654030 prefixEnd_654030 := by exact prefixLift 654030
  have htrace : WordTrace (prefixWord ++ tailWord_654030) baseStart_654030 baseEnd_654030 := by
    simpa [prefixWord, tailWord_654030, baseEnd_654030] using wordTrace_append hprefix tailTrace_654030
  have hstable : (prefixWord ++ tailWord_654030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654030).length < 2 ^ (prefixWord ++ tailWord_654030).sum := by decide
  have hdescent : baseEnd_654030 < baseStart_654030 := by decide
  rcases family_descends (prefixWord ++ tailWord_654030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654072 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 8]
def baseStart_654072 : Nat := 118140960795 + 654072 * 2 ^ 59
def prefixEnd_654072 : Nat := 4983230072969 + 3 ^ 40 * 654072 * 2
def baseEnd_654072 : Nat := 149268141621186743996437

theorem tailTrace_654072 : CollatzResearch.WordTrace tailWord_654072 prefixEnd_654072 149268141621186743996437 := by
  unfold tailWord_654072
  simp only [CollatzResearch.WordTrace]
  refine ⟨11927982843208162724646235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15903977124277550299528313 11927982843208162724646235)
  ·
    refine ⟨17891974264812244086969353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11927982843208162724646235 17891974264812244086969353)
    ·
      refine ⟨13418980698609183065227015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17891974264812244086969353 13418980698609183065227015)
      ·
        refine ⟨20128471047913774597840523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13418980698609183065227015 20128471047913774597840523)
        ·
          refine ⟨30192706571870661896760785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20128471047913774597840523 30192706571870661896760785)
          ·
            refine ⟨22644529928902996422570589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30192706571870661896760785 22644529928902996422570589)
            ·
              refine ⟨8491698723338623658463971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22644529928902996422570589 8491698723338623658463971)
              ·
                refine ⟨12737548085007935487695957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8491698723338623658463971 12737548085007935487695957)
                ·
                  refine ⟨149268141621186743996437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12737548085007935487695957 149268141621186743996437)
                  ·
                    rfl

theorem cell21_654072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_654072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654072 prefixEnd_654072 := by exact prefixLift 654072
  have htrace : WordTrace (prefixWord ++ tailWord_654072) baseStart_654072 baseEnd_654072 := by
    simpa [prefixWord, tailWord_654072, baseEnd_654072] using wordTrace_append hprefix tailTrace_654072
  have hstable : (prefixWord ++ tailWord_654072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654072).length < 2 ^ (prefixWord ++ tailWord_654072).sum := by decide
  have hdescent : baseEnd_654072 < baseStart_654072 := by decide
  rcases family_descends (prefixWord ++ tailWord_654072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654165 : List Nat := [1, 3, 2, 2, 2, 1, 1, 5, 4]
def baseStart_654165 : Nat := 118140960795 + 654165 * 2 ^ 59
def prefixEnd_654165 : Nat := 4983230072969 + 3 ^ 40 * 654165 * 2
def baseEnd_654165 : Nat := 149289365488239248946247

theorem tailTrace_654165 : CollatzResearch.WordTrace tailWord_654165 prefixEnd_654165 149289365488239248946247 := by
  unfold tailWord_654165
  simp only [CollatzResearch.WordTrace]
  refine ⟨23859357675079402332427949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15906238450052934888285299 23859357675079402332427949)
  ·
    refine ⟨8947259128154775874660481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23859357675079402332427949 8947259128154775874660481)
    ·
      refine ⟨6710444346116081905995361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8947259128154775874660481 6710444346116081905995361)
      ·
        refine ⟨5032833259587061429496521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6710444346116081905995361 5032833259587061429496521)
        ·
          refine ⟨3774624944690296072122391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5032833259587061429496521 3774624944690296072122391)
          ·
            refine ⟨5661937417035444108183587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3774624944690296072122391 5661937417035444108183587)
            ·
              refine ⟨8492906125553166162275381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5661937417035444108183587 8492906125553166162275381)
              ·
                refine ⟨796209949270609327713317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8492906125553166162275381 796209949270609327713317)
                ·
                  refine ⟨149289365488239248946247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 796209949270609327713317 149289365488239248946247)
                  ·
                    rfl

theorem cell21_654165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_654165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654165 prefixEnd_654165 := by exact prefixLift 654165
  have htrace : WordTrace (prefixWord ++ tailWord_654165) baseStart_654165 baseEnd_654165 := by
    simpa [prefixWord, tailWord_654165, baseEnd_654165] using wordTrace_append hprefix tailTrace_654165
  have hstable : (prefixWord ++ tailWord_654165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654165).length < 2 ^ (prefixWord ++ tailWord_654165).sum := by decide
  have hdescent : baseEnd_654165 < baseStart_654165 := by decide
  rcases family_descends (prefixWord ++ tailWord_654165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654230 : List Nat := [5, 3, 1, 1, 1, 2, 1, 7]
def baseStart_654230 : Nat := 118140960795 + 654230 * 2 ^ 59
def prefixEnd_654230 : Nat := 4983230072969 + 3 ^ 40 * 654230 * 2
def baseEnd_654230 : Nat := 49768066457937860120927

theorem tailTrace_654230 : CollatzResearch.WordTrace tailWord_654230 prefixEnd_654230 49768066457937860120927 := by
  unfold tailWord_654230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1491358026240244902096509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15907818946562612289029429 1491358026240244902096509)
  ·
    refine ⟨559259259840091838286191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1491358026240244902096509 559259259840091838286191)
    ·
      refine ⟨838888889760137757429287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 559259259840091838286191 838888889760137757429287)
      ·
        refine ⟨1258333334640206636143931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 838888889760137757429287 1258333334640206636143931)
        ·
          refine ⟨1887500001960309954215897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258333334640206636143931 1887500001960309954215897)
          ·
            refine ⟨1415625001470232465661923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1887500001960309954215897 1415625001470232465661923)
            ·
              refine ⟨2123437502205348698492885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415625001470232465661923 2123437502205348698492885)
              ·
                refine ⟨49768066457937860120927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2123437502205348698492885 49768066457937860120927)
                ·
                  rfl

theorem cell21_654230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_654230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654230 prefixEnd_654230 := by exact prefixLift 654230
  have htrace : WordTrace (prefixWord ++ tailWord_654230) baseStart_654230 baseEnd_654230 := by
    simpa [prefixWord, tailWord_654230, baseEnd_654230] using wordTrace_append hprefix tailTrace_654230
  have hstable : (prefixWord ++ tailWord_654230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654230).length < 2 ^ (prefixWord ++ tailWord_654230).sum := by decide
  have hdescent : baseEnd_654230 < baseStart_654230 := by decide
  rcases family_descends (prefixWord ++ tailWord_654230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654241 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 6]
def baseStart_654241 : Nat := 118140960795 + 654241 * 2 ^ 59
def prefixEnd_654241 : Nat := 4983230072969 + 3 ^ 40 * 654241 * 2
def baseEnd_654241 : Nat := 149306709723680005679425

theorem tailTrace_654241 : CollatzResearch.WordTrace tailWord_654241 prefixEnd_654241 149306709723680005679425 := by
  unfold tailWord_654241
  simp only [CollatzResearch.WordTrace]
  refine ⟨23862129622804067312194577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15908086415202711541463051 23862129622804067312194577)
  ·
    refine ⟨17896597217103050484145933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23862129622804067312194577 17896597217103050484145933)
    ·
      refine ⟨6711223956413643931554725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17896597217103050484145933 6711223956413643931554725)
      ·
        refine ⟨1258354491827558237166511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6711223956413643931554725 1258354491827558237166511)
        ·
          refine ⟨1887531737741337355749767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258354491827558237166511 1887531737741337355749767)
          ·
            refine ⟨2831297606612006033624651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1887531737741337355749767 2831297606612006033624651)
            ·
              refine ⟨4246946409918009050436977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2831297606612006033624651 4246946409918009050436977)
              ·
                refine ⟨3185209807438506787827733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4246946409918009050436977 3185209807438506787827733)
                ·
                  refine ⟨149306709723680005679425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3185209807438506787827733 149306709723680005679425)
                  ·
                    rfl

theorem cell21_654241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_654241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654241 prefixEnd_654241 := by exact prefixLift 654241
  have htrace : WordTrace (prefixWord ++ tailWord_654241) baseStart_654241 baseEnd_654241 := by
    simpa [prefixWord, tailWord_654241, baseEnd_654241] using wordTrace_append hprefix tailTrace_654241
  have hstable : (prefixWord ++ tailWord_654241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654241).length < 2 ^ (prefixWord ++ tailWord_654241).sum := by decide
  have hdescent : baseEnd_654241 < baseStart_654241 := by decide
  rcases family_descends (prefixWord ++ tailWord_654241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654348 : List Nat := [2, 2, 1, 2, 3, 3, 3, 5]
def baseStart_654348 : Nat := 118140960795 + 654348 * 2 ^ 59
def prefixEnd_654348 : Nat := 4983230072969 + 3 ^ 40 * 654348 * 2
def baseEnd_654348 : Nat := 49777042860490532465291

theorem tailTrace_654348 : CollatzResearch.WordTrace tailWord_654348 prefixEnd_654348 49777042860490532465291 := by
  unfold tailWord_654348
  simp only [CollatzResearch.WordTrace]
  refine ⟨11933016116708212293169849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15910688155610949724226465 11933016116708212293169849)
  ·
    refine ⟨8949762087531159219877387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11933016116708212293169849 8949762087531159219877387)
    ·
      refine ⟨13424643131296738829816081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8949762087531159219877387 13424643131296738829816081)
      ·
        refine ⟨10068482348472554122362061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13424643131296738829816081 10068482348472554122362061)
        ·
          refine ⟨3775680880677207795885773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10068482348472554122362061 3775680880677207795885773)
          ·
            refine ⟨1415880330253952923457165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3775680880677207795885773 1415880330253952923457165)
            ·
              refine ⟨530955123845232346296437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1415880330253952923457165 530955123845232346296437)
              ·
                refine ⟨49777042860490532465291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 530955123845232346296437 49777042860490532465291)
                ·
                  rfl

theorem cell21_654348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 5].length) (baseStart_654348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654348 prefixEnd_654348 := by exact prefixLift 654348
  have htrace : WordTrace (prefixWord ++ tailWord_654348) baseStart_654348 baseEnd_654348 := by
    simpa [prefixWord, tailWord_654348, baseEnd_654348] using wordTrace_append hprefix tailTrace_654348
  have hstable : (prefixWord ++ tailWord_654348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654348).length < 2 ^ (prefixWord ++ tailWord_654348).sum := by decide
  have hdescent : baseEnd_654348 < baseStart_654348 := by decide
  rcases family_descends (prefixWord ++ tailWord_654348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654368 : List Nat := [2, 1, 1, 7, 2, 1, 1, 2, 4]
def baseStart_654368 : Nat := 118140960795 + 654368 * 2 ^ 59
def prefixEnd_654368 : Nat := 4983230072969 + 3 ^ 40 * 654368 * 2
def baseEnd_654368 : Nat := 149335692853956007062499

theorem tailTrace_654368 : CollatzResearch.WordTrace tailWord_654368 prefixEnd_654368 149335692853956007062499 := by
  unfold tailWord_654368
  simp only [CollatzResearch.WordTrace]
  refine ⟨11933380846671984001033879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15911174462229312001378505 11933380846671984001033879)
  ·
    refine ⟨17900071270007976001550819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11933380846671984001033879 17900071270007976001550819)
    ·
      refine ⟨26850106905011964002326229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17900071270007976001550819 26850106905011964002326229)
      ·
        refine ⟨629299380586217906304521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 26850106905011964002326229 629299380586217906304521)
        ·
          refine ⟨471974535439663429728391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 629299380586217906304521 471974535439663429728391)
          ·
            refine ⟨707961803159495144592587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471974535439663429728391 707961803159495144592587)
            ·
              refine ⟨1061942704739242716888881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707961803159495144592587 1061942704739242716888881)
              ·
                refine ⟨796457028554432037666661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061942704739242716888881 796457028554432037666661)
                ·
                  refine ⟨149335692853956007062499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 796457028554432037666661 149335692853956007062499)
                  ·
                    rfl

theorem cell21_654368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 4].length) (baseStart_654368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654368 prefixEnd_654368 := by exact prefixLift 654368
  have htrace : WordTrace (prefixWord ++ tailWord_654368) baseStart_654368 baseEnd_654368 := by
    simpa [prefixWord, tailWord_654368, baseEnd_654368] using wordTrace_append hprefix tailTrace_654368
  have hstable : (prefixWord ++ tailWord_654368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654368).length < 2 ^ (prefixWord ++ tailWord_654368).sum := by decide
  have hdescent : baseEnd_654368 < baseStart_654368 := by decide
  rcases family_descends (prefixWord ++ tailWord_654368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654407 : List Nat := [1, 1, 4, 1, 3, 3, 1, 7]
def baseStart_654407 : Nat := 118140960795 + 654407 * 2 ^ 59
def prefixEnd_654407 : Nat := 4983230072969 + 3 ^ 40 * 654407 * 2
def baseEnd_654407 : Nat := 49781531061766868637473

theorem tailTrace_654407 : CollatzResearch.WordTrace tailWord_654407 prefixEnd_654407 49781531061766868637473 := by
  unfold tailWord_654407
  simp only [CollatzResearch.WordTrace]
  refine ⟨23868184140202677662737475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15912122760135118441824983 23868184140202677662737475)
  ·
    refine ⟨35802276210304016494106213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23868184140202677662737475 35802276210304016494106213)
    ·
      refine ⟨6712926789432003092644915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35802276210304016494106213 6712926789432003092644915)
      ·
        refine ⟨10069390184148004638967373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6712926789432003092644915 10069390184148004638967373)
        ·
          refine ⟨3776021319055501739612765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10069390184148004638967373 3776021319055501739612765)
          ·
            refine ⟨1416007994645813152354787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3776021319055501739612765 1416007994645813152354787)
            ·
              refine ⟨2124011991968719728532181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416007994645813152354787 2124011991968719728532181)
              ·
                refine ⟨49781531061766868637473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2124011991968719728532181 49781531061766868637473)
                ·
                  rfl

theorem cell21_654407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 7].length) (baseStart_654407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654407 prefixEnd_654407 := by exact prefixLift 654407
  have htrace : WordTrace (prefixWord ++ tailWord_654407) baseStart_654407 baseEnd_654407 := by
    simpa [prefixWord, tailWord_654407, baseEnd_654407] using wordTrace_append hprefix tailTrace_654407
  have hstable : (prefixWord ++ tailWord_654407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654407).length < 2 ^ (prefixWord ++ tailWord_654407).sum := by decide
  have hdescent : baseEnd_654407 < baseStart_654407 := by decide
  rcases family_descends (prefixWord ++ tailWord_654407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654413 : List Nat := [1, 6, 1, 1, 1, 4, 1, 3, 3]
def baseStart_654413 : Nat := 118140960795 + 654413 * 2 ^ 59
def prefixEnd_654413 : Nat := 4983230072969 + 3 ^ 40 * 654413 * 2
def baseEnd_654413 : Nat := 149345962467045928812407

theorem tailTrace_654413 : CollatzResearch.WordTrace tailWord_654413 prefixEnd_654413 149345962467045928812407 := by
  unfold tailWord_654413
  simp only [CollatzResearch.WordTrace]
  refine ⟨23868402978180940687455893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15912268652120627124970595 23868402978180940687455893)
  ·
    refine ⟨1118831389602231594724495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23868402978180940687455893 1118831389602231594724495)
    ·
      refine ⟨1678247084403347392086743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1118831389602231594724495 1678247084403347392086743)
      ·
        refine ⟨2517370626605021088130115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1678247084403347392086743 2517370626605021088130115)
        ·
          refine ⟨3776055939907531632195173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2517370626605021088130115 3776055939907531632195173)
          ·
            refine ⟨708010488732662181036595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3776055939907531632195173 708010488732662181036595)
            ·
              refine ⟨1062015733098993271554893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708010488732662181036595 1062015733098993271554893)
              ·
                refine ⟨398255899912122476833085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1062015733098993271554893 398255899912122476833085)
                ·
                  refine ⟨149345962467045928812407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398255899912122476833085 149345962467045928812407)
                  ·
                    rfl

theorem cell21_654413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_654413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654413 prefixEnd_654413 := by exact prefixLift 654413
  have htrace : WordTrace (prefixWord ++ tailWord_654413) baseStart_654413 baseEnd_654413 := by
    simpa [prefixWord, tailWord_654413, baseEnd_654413] using wordTrace_append hprefix tailTrace_654413
  have hstable : (prefixWord ++ tailWord_654413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654413).length < 2 ^ (prefixWord ++ tailWord_654413).sum := by decide
  have hdescent : baseEnd_654413 < baseStart_654413 := by decide
  rcases family_descends (prefixWord ++ tailWord_654413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654500 : List Nat := [2, 3, 1, 2, 3, 3, 1, 6]
def baseStart_654500 : Nat := 118140960795 + 654500 * 2 ^ 59
def prefixEnd_654500 : Nat := 4983230072969 + 3 ^ 40 * 654500 * 2
def baseEnd_654500 : Nat := 49788605684117703620743

theorem tailTrace_654500 : CollatzResearch.WordTrace tailWord_654500 prefixEnd_654500 49788605684117703620743 := by
  unfold tailWord_654500
  simp only [CollatzResearch.WordTrace]
  refine ⟨11935788064432877272936477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15914384085910503030581969 11935788064432877272936477)
  ·
    refine ⟨4475920524162328977351179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11935788064432877272936477 4475920524162328977351179)
    ·
      refine ⟨6713880786243493466026769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4475920524162328977351179 6713880786243493466026769)
      ·
        refine ⟨5035410589682620099520077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6713880786243493466026769 5035410589682620099520077)
        ·
          refine ⟨1888278971130982537320029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5035410589682620099520077 1888278971130982537320029)
          ·
            refine ⟨708104614174118451495011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1888278971130982537320029 708104614174118451495011)
            ·
              refine ⟨1062156921261177677242517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708104614174118451495011 1062156921261177677242517)
              ·
                refine ⟨49788605684117703620743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1062156921261177677242517 49788605684117703620743)
                ·
                  rfl

theorem cell21_654500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 6].length) (baseStart_654500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654500 prefixEnd_654500 := by exact prefixLift 654500
  have htrace : WordTrace (prefixWord ++ tailWord_654500) baseStart_654500 baseEnd_654500 := by
    simpa [prefixWord, tailWord_654500, baseEnd_654500] using wordTrace_append hprefix tailTrace_654500
  have hstable : (prefixWord ++ tailWord_654500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654500).length < 2 ^ (prefixWord ++ tailWord_654500).sum := by decide
  have hdescent : baseEnd_654500 < baseStart_654500 := by decide
  rcases family_descends (prefixWord ++ tailWord_654500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654514 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_654514 : Nat := 118140960795 + 654514 * 2 ^ 59
def prefixEnd_654514 : Nat := 4983230072969 + 3 ^ 40 * 654514 * 2
def baseEnd_654514 : Nat := 149369012043092197628867

theorem tailTrace_654514 : CollatzResearch.WordTrace tailWord_654514 prefixEnd_654514 149369012043092197628867 := by
  unfold tailWord_654514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5968021687703758734220649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15914724500543356624588397 5968021687703758734220649)
  ·
    refine ⟨4476016265777819050665487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5968021687703758734220649 4476016265777819050665487)
    ·
      refine ⟨6714024398666728575998231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4476016265777819050665487 6714024398666728575998231)
      ·
        refine ⟨10071036598000092863997347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6714024398666728575998231 10071036598000092863997347)
        ·
          refine ⟨15106554897000139295996021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10071036598000092863997347 15106554897000139295996021)
          ·
            refine ⟨1416239521593763058999627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15106554897000139295996021 1416239521593763058999627)
            ·
              refine ⟨2124359282390644588499441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416239521593763058999627 2124359282390644588499441)
              ·
                refine ⟨1593269461792983441374581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2124359282390644588499441 1593269461792983441374581)
                ·
                  refine ⟨149369012043092197628867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1593269461792983441374581 149369012043092197628867)
                  ·
                    rfl

theorem cell21_654514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_654514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654514 prefixEnd_654514 := by exact prefixLift 654514
  have htrace : WordTrace (prefixWord ++ tailWord_654514) baseStart_654514 baseEnd_654514 := by
    simpa [prefixWord, tailWord_654514, baseEnd_654514] using wordTrace_append hprefix tailTrace_654514
  have hstable : (prefixWord ++ tailWord_654514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654514).length < 2 ^ (prefixWord ++ tailWord_654514).sum := by decide
  have hdescent : baseEnd_654514 < baseStart_654514 := by decide
  rcases family_descends (prefixWord ++ tailWord_654514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654534 : List Nat := [6, 1, 2, 2, 1, 1, 8]
def baseStart_654534 : Nat := 118140960795 + 654534 * 2 ^ 59
def prefixEnd_654534 : Nat := 4983230072969 + 3 ^ 40 * 654534 * 2
def baseEnd_654534 : Nat := 16597064035064067477277

theorem tailTrace_654534 : CollatzResearch.WordTrace tailWord_654534 prefixEnd_654534 16597064035064067477277 := by
  unfold tailWord_654534
  simp only [CollatzResearch.WordTrace]
  refine ⟨746025506585705573519083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15915210807161718901740437 746025506585705573519083)
  ·
    refine ⟨1119038259878558360278625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 746025506585705573519083 1119038259878558360278625)
    ·
      refine ⟨839278694908918770208969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1119038259878558360278625 839278694908918770208969)
      ·
        refine ⟨629459021181689077656727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 839278694908918770208969 629459021181689077656727)
        ·
          refine ⟨944188531772533616485091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629459021181689077656727 944188531772533616485091)
          ·
            refine ⟨1416282797658800424727637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944188531772533616485091 1416282797658800424727637)
            ·
              refine ⟨16597064035064067477277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1416282797658800424727637 16597064035064067477277)
              ·
                rfl

theorem cell21_654534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 8].length) (baseStart_654534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654534 prefixEnd_654534 := by exact prefixLift 654534
  have htrace : WordTrace (prefixWord ++ tailWord_654534) baseStart_654534 baseEnd_654534 := by
    simpa [prefixWord, tailWord_654534, baseEnd_654534] using wordTrace_append hprefix tailTrace_654534
  have hstable : (prefixWord ++ tailWord_654534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654534).length < 2 ^ (prefixWord ++ tailWord_654534).sum := by decide
  have hdescent : baseEnd_654534 < baseStart_654534 := by decide
  rcases family_descends (prefixWord ++ tailWord_654534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654548 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 5]
def baseStart_654548 : Nat := 118140960795 + 654548 * 2 ^ 59
def prefixEnd_654548 : Nat := 4983230072969 + 3 ^ 40 * 654548 * 2
def baseEnd_654548 : Nat := 149376771306315694062131

theorem tailTrace_654548 : CollatzResearch.WordTrace tailWord_654548 prefixEnd_654548 149376771306315694062131 := by
  unfold tailWord_654548
  simp only [CollatzResearch.WordTrace]
  refine ⟨11936663416345929371810149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15915551221794572495746865 11936663416345929371810149)
  ·
    refine ⟨2238124390564861757214403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11936663416345929371810149 2238124390564861757214403)
    ·
      refine ⟨3357186585847292635821605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2238124390564861757214403 3357186585847292635821605)
      ·
        refine ⟨629472484846367369216551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3357186585847292635821605 629472484846367369216551)
        ·
          refine ⟨944208727269551053824827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629472484846367369216551 944208727269551053824827)
          ·
            refine ⟨1416313090904326580737241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944208727269551053824827 1416313090904326580737241)
            ·
              refine ⟨1062234818178244935552931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1416313090904326580737241 1062234818178244935552931)
              ·
                refine ⟨1593352227267367403329397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062234818178244935552931 1593352227267367403329397)
                ·
                  refine ⟨149376771306315694062131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1593352227267367403329397 149376771306315694062131)
                  ·
                    rfl

theorem cell21_654548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_654548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654548 prefixEnd_654548 := by exact prefixLift 654548
  have htrace : WordTrace (prefixWord ++ tailWord_654548) baseStart_654548 baseEnd_654548 := by
    simpa [prefixWord, tailWord_654548, baseEnd_654548] using wordTrace_append hprefix tailTrace_654548
  have hstable : (prefixWord ++ tailWord_654548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654548).length < 2 ^ (prefixWord ++ tailWord_654548).sum := by decide
  have hdescent : baseEnd_654548 < baseStart_654548 := by decide
  rcases family_descends (prefixWord ++ tailWord_654548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654604 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 6]
def baseStart_654604 : Nat := 118140960795 + 654604 * 2 ^ 59
def prefixEnd_654604 : Nat := 4983230072969 + 3 ^ 40 * 654604 * 2
def baseEnd_654604 : Nat := 149389551269272041128683

theorem tailTrace_654604 : CollatzResearch.WordTrace tailWord_654604 prefixEnd_654604 149389551269272041128683 := by
  unfold tailWord_654604
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937684660244490153829433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15916912880325986871772577 11937684660244490153829433)
  ·
    refine ⟨8953263495183367615372075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11937684660244490153829433 8953263495183367615372075)
    ·
      refine ⟨13429895242775051423058113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8953263495183367615372075 13429895242775051423058113)
      ·
        refine ⟨10072421432081288567293585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13429895242775051423058113 10072421432081288567293585)
        ·
          refine ⟨7554316074060966425470189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10072421432081288567293585 7554316074060966425470189)
          ·
            refine ⟨2832868527772862409551321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7554316074060966425470189 2832868527772862409551321)
            ·
              refine ⟨2124651395829646807163491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2832868527772862409551321 2124651395829646807163491)
              ·
                refine ⟨3186977093744470210745237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124651395829646807163491 3186977093744470210745237)
                ·
                  refine ⟨149389551269272041128683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3186977093744470210745237 149389551269272041128683)
                  ·
                    rfl

theorem cell21_654604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_654604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654604 prefixEnd_654604 := by exact prefixLift 654604
  have htrace : WordTrace (prefixWord ++ tailWord_654604) baseStart_654604 baseEnd_654604 := by
    simpa [prefixWord, tailWord_654604, baseEnd_654604] using wordTrace_append hprefix tailTrace_654604
  have hstable : (prefixWord ++ tailWord_654604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654604).length < 2 ^ (prefixWord ++ tailWord_654604).sum := by decide
  have hdescent : baseEnd_654604 < baseStart_654604 := by decide
  rcases family_descends (prefixWord ++ tailWord_654604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654680 : List Nat := [2, 1, 2, 2, 1, 1, 3, 5, 4]
def baseStart_654680 : Nat := 118140960795 + 654680 * 2 ^ 59
def prefixEnd_654680 : Nat := 4983230072969 + 3 ^ 40 * 654680 * 2
def baseEnd_654680 : Nat := 149406895504712797861861

theorem tailTrace_654680 : CollatzResearch.WordTrace tailWord_654680 prefixEnd_654680 149406895504712797861861 := by
  unfold tailWord_654680
  simp only [CollatzResearch.WordTrace]
  refine ⟨11939070634106822643712747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15918760845475763524950329 11939070634106822643712747)
  ·
    refine ⟨17908605951160233965569121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11939070634106822643712747 17908605951160233965569121)
    ·
      refine ⟨13431454463370175474176841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17908605951160233965569121 13431454463370175474176841)
      ·
        refine ⟨10073590847527631605632631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13431454463370175474176841 10073590847527631605632631)
        ·
          refine ⟨15110386271291447408448947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10073590847527631605632631 15110386271291447408448947)
          ·
            refine ⟨22665579406937171112673421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15110386271291447408448947 22665579406937171112673421)
            ·
              refine ⟨8499592277601439167252533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22665579406937171112673421 8499592277601439167252533)
              ·
                refine ⟨796836776025134921929925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8499592277601439167252533 796836776025134921929925)
                ·
                  refine ⟨149406895504712797861861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 796836776025134921929925 149406895504712797861861)
                  ·
                    rfl

theorem cell21_654680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_654680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654680 prefixEnd_654680 := by exact prefixLift 654680
  have htrace : WordTrace (prefixWord ++ tailWord_654680) baseStart_654680 baseEnd_654680 := by
    simpa [prefixWord, tailWord_654680, baseEnd_654680] using wordTrace_append hprefix tailTrace_654680
  have hstable : (prefixWord ++ tailWord_654680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654680).length < 2 ^ (prefixWord ++ tailWord_654680).sum := by decide
  have hdescent : baseEnd_654680 < baseStart_654680 := by decide
  rcases family_descends (prefixWord ++ tailWord_654680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654725 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 5]
def baseStart_654725 : Nat := 118140960795 + 654725 * 2 ^ 59
def prefixEnd_654725 : Nat := 4983230072969 + 3 ^ 40 * 654725 * 2
def baseEnd_654725 : Nat := 149417165117802719611769

theorem tailTrace_654725 : CollatzResearch.WordTrace tailWord_654725 prefixEnd_654725 149417165117802719611769 := by
  unfold tailWord_654725
  simp only [CollatzResearch.WordTrace]
  refine ⟨23879782553050617972813629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15919855035367078648542419 23879782553050617972813629)
  ·
    refine ⟨8954918457393981739805111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23879782553050617972813629 8954918457393981739805111)
    ·
      refine ⟨13432377686090972609707667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8954918457393981739805111 13432377686090972609707667)
      ·
        refine ⟨20148566529136458914561501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13432377686090972609707667 20148566529136458914561501)
        ·
          refine ⟨7555712448426172092960563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20148566529136458914561501 7555712448426172092960563)
          ·
            refine ⟨11333568672639258139440845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7555712448426172092960563 11333568672639258139440845)
            ·
              refine ⟨4250088252239721802290317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11333568672639258139440845 4250088252239721802290317)
              ·
                refine ⟨1593783094589895675858869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4250088252239721802290317 1593783094589895675858869)
                ·
                  refine ⟨149417165117802719611769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1593783094589895675858869 149417165117802719611769)
                  ·
                    rfl

theorem cell21_654725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_654725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654725 prefixEnd_654725 := by exact prefixLift 654725
  have htrace : WordTrace (prefixWord ++ tailWord_654725) baseStart_654725 baseEnd_654725 := by
    simpa [prefixWord, tailWord_654725, baseEnd_654725] using wordTrace_append hprefix tailTrace_654725
  have hstable : (prefixWord ++ tailWord_654725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654725).length < 2 ^ (prefixWord ++ tailWord_654725).sum := by decide
  have hdescent : baseEnd_654725 < baseStart_654725 := by decide
  rcases family_descends (prefixWord ++ tailWord_654725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654832 : List Nat := [2, 1, 1, 1, 3, 4, 1, 4, 4]
def baseStart_654832 : Nat := 118140960795 + 654832 * 2 ^ 59
def prefixEnd_654832 : Nat := 4983230072969 + 3 ^ 40 * 654832 * 2
def baseEnd_654832 : Nat := 149441583975594311328217

theorem tailTrace_654832 : CollatzResearch.WordTrace tailWord_654832 prefixEnd_654832 149441583975594311328217 := by
  unfold tailWord_654832
  simp only [CollatzResearch.WordTrace]
  refine ⟨11941842581831487623479375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15922456775775316831305833 11941842581831487623479375)
  ·
    refine ⟨17912763872747231435219063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11941842581831487623479375 17912763872747231435219063)
    ·
      refine ⟨26869145809120847152828595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17912763872747231435219063 26869145809120847152828595)
      ·
        refine ⟨40303718713681270729242893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26869145809120847152828595 40303718713681270729242893)
        ·
          refine ⟨15113894517630476523466085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40303718713681270729242893 15113894517630476523466085)
          ·
            refine ⟨2833855222055714348149891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15113894517630476523466085 2833855222055714348149891)
            ·
              refine ⟨4250782833083571522224837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833855222055714348149891 4250782833083571522224837)
              ·
                refine ⟨797021781203169660417157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4250782833083571522224837 797021781203169660417157)
                ·
                  refine ⟨149441583975594311328217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797021781203169660417157 149441583975594311328217)
                  ·
                    rfl

theorem cell21_654832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_654832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654832 prefixEnd_654832 := by exact prefixLift 654832
  have htrace : WordTrace (prefixWord ++ tailWord_654832) baseStart_654832 baseEnd_654832 := by
    simpa [prefixWord, tailWord_654832, baseEnd_654832] using wordTrace_append hprefix tailTrace_654832
  have hstable : (prefixWord ++ tailWord_654832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654832).length < 2 ^ (prefixWord ++ tailWord_654832).sum := by decide
  have hdescent : baseEnd_654832 < baseStart_654832 := by decide
  rcases family_descends (prefixWord ++ tailWord_654832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654877 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 7]
def baseStart_654877 : Nat := 118140960795 + 654877 * 2 ^ 59
def prefixEnd_654877 : Nat := 4983230072969 + 3 ^ 40 * 654877 * 2
def baseEnd_654877 : Nat := 149451853588684233078125

theorem tailTrace_654877 : CollatzResearch.WordTrace tailWord_654877 prefixEnd_654877 149451853588684233078125 := by
  unfold tailWord_654877
  simp only [CollatzResearch.WordTrace]
  refine ⟨23885326448499947932346885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15923550965666631954897923 23885326448499947932346885)
  ·
    refine ⟨4478498709093740237315041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23885326448499947932346885 4478498709093740237315041)
    ·
      refine ⟨3358874031820305177986281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4478498709093740237315041 3358874031820305177986281)
      ·
        refine ⟨2519155523865228883489711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3358874031820305177986281 2519155523865228883489711)
        ·
          refine ⟨3778733285797843325234567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2519155523865228883489711 3778733285797843325234567)
          ·
            refine ⟨5668099928696764987851851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3778733285797843325234567 5668099928696764987851851)
            ·
              refine ⟨8502149893045147481777777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5668099928696764987851851 8502149893045147481777777)
              ·
                refine ⟨6376612419783860611333333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8502149893045147481777777 6376612419783860611333333)
                ·
                  refine ⟨149451853588684233078125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6376612419783860611333333 149451853588684233078125)
                  ·
                    rfl

theorem cell21_654877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_654877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654877 prefixEnd_654877 := by exact prefixLift 654877
  have htrace : WordTrace (prefixWord ++ tailWord_654877) baseStart_654877 baseEnd_654877 := by
    simpa [prefixWord, tailWord_654877, baseEnd_654877] using wordTrace_append hprefix tailTrace_654877
  have hstable : (prefixWord ++ tailWord_654877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654877).length < 2 ^ (prefixWord ++ tailWord_654877).sum := by decide
  have hdescent : baseEnd_654877 < baseStart_654877 := by decide
  rcases family_descends (prefixWord ++ tailWord_654877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654894 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_654894 : Nat := 118140960795 + 654894 * 2 ^ 59
def prefixEnd_654894 : Nat := 4983230072969 + 3 ^ 40 * 654894 * 2
def baseEnd_654894 : Nat := 149455733220295981294757

theorem tailTrace_654894 : CollatzResearch.WordTrace tailWord_654894 prefixEnd_654894 149455733220295981294757 := by
  unfold tailWord_654894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2985743311179794979464467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15923964326292239890477157 2985743311179794979464467)
  ·
    refine ⟨4478614966769692469196701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2985743311179794979464467 4478614966769692469196701)
    ·
      refine ⟨1679480612538634675948763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4478614966769692469196701 1679480612538634675948763)
      ·
        refine ⟨2519220918807952013923145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1679480612538634675948763 2519220918807952013923145)
        ·
          refine ⟨1889415689105964010442359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2519220918807952013923145 1889415689105964010442359)
          ·
            refine ⟨2834123533658946015663539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889415689105964010442359 2834123533658946015663539)
            ·
              refine ⟨4251185300488419023495309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834123533658946015663539 4251185300488419023495309)
              ·
                refine ⟨1594194487683157133810741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4251185300488419023495309 1594194487683157133810741)
                ·
                  refine ⟨149455733220295981294757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1594194487683157133810741 149455733220295981294757)
                  ·
                    rfl

theorem cell21_654894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_654894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654894 prefixEnd_654894 := by exact prefixLift 654894
  have htrace : WordTrace (prefixWord ++ tailWord_654894) baseStart_654894 baseEnd_654894 := by
    simpa [prefixWord, tailWord_654894, baseEnd_654894] using wordTrace_append hprefix tailTrace_654894
  have hstable : (prefixWord ++ tailWord_654894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654894).length < 2 ^ (prefixWord ++ tailWord_654894).sum := by decide
  have hdescent : baseEnd_654894 < baseStart_654894 := by decide
  rcases family_descends (prefixWord ++ tailWord_654894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654922 : List Nat := [3, 1, 2, 1, 1, 3, 3, 7]
def baseStart_654922 : Nat := 118140960795 + 654922 * 2 ^ 59
def prefixEnd_654922 : Nat := 4983230072969 + 3 ^ 40 * 654922 * 2
def baseEnd_654922 : Nat := 49820707733924718276011

theorem tailTrace_654922 : CollatzResearch.WordTrace tailWord_654922 prefixEnd_654922 49820707733924718276011 := by
  unfold tailWord_654922
  simp only [CollatzResearch.WordTrace]
  refine ⟨5971741933334230154433755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15924645155557947078490013 5971741933334230154433755)
  ·
    refine ⟨8957612900001345231650633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5971741933334230154433755 8957612900001345231650633)
    ·
      refine ⟨6718209675001008923737975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8957612900001345231650633 6718209675001008923737975)
      ·
        refine ⟨10077314512501513385606963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6718209675001008923737975 10077314512501513385606963)
        ·
          refine ⟨15115971768752270078410445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10077314512501513385606963 15115971768752270078410445)
          ·
            refine ⟨5668489413282101279403917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15115971768752270078410445 5668489413282101279403917)
            ·
              refine ⟨2125683529980787979776469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5668489413282101279403917 2125683529980787979776469)
              ·
                refine ⟨49820707733924718276011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2125683529980787979776469 49820707733924718276011)
                ·
                  rfl

theorem cell21_654922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_654922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654922 prefixEnd_654922 := by exact prefixLift 654922
  have htrace : WordTrace (prefixWord ++ tailWord_654922) baseStart_654922 baseEnd_654922 := by
    simpa [prefixWord, tailWord_654922, baseEnd_654922] using wordTrace_append hprefix tailTrace_654922
  have hstable : (prefixWord ++ tailWord_654922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654922).length < 2 ^ (prefixWord ++ tailWord_654922).sum := by decide
  have hdescent : baseEnd_654922 < baseStart_654922 := by decide
  rcases family_descends (prefixWord ++ tailWord_654922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_654953 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 5]
def baseStart_654953 : Nat := 118140960795 + 654953 * 2 ^ 59
def prefixEnd_654953 : Nat := 4983230072969 + 3 ^ 40 * 654953 * 2
def baseEnd_654953 : Nat := 149469197824124989811303

theorem tailTrace_654953 : CollatzResearch.WordTrace tailWord_654953 prefixEnd_654953 149469197824124989811303 := by
  unfold tailWord_654953
  simp only [CollatzResearch.WordTrace]
  refine ⟨23888098396224612912113513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15925398930816408608075675 23888098396224612912113513)
  ·
    refine ⟨17916073797168459684085135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23888098396224612912113513 17916073797168459684085135)
    ·
      refine ⟨26874110695752689526127703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17916073797168459684085135 26874110695752689526127703)
      ·
        refine ⟨40311166043629034289191555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26874110695752689526127703 40311166043629034289191555)
        ·
          refine ⟨60466749065443551433787333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40311166043629034289191555 60466749065443551433787333)
          ·
            refine ⟨11337515449770665893835125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60466749065443551433787333 11337515449770665893835125)
            ·
              refine ⟨1062892073415999927547043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11337515449770665893835125 1062892073415999927547043)
              ·
                refine ⟨1594338110123999891320565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062892073415999927547043 1594338110123999891320565)
                ·
                  refine ⟨149469197824124989811303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1594338110123999891320565 149469197824124989811303)
                  ·
                    rfl

theorem cell21_654953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_654953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_654953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_654953 prefixEnd_654953 := by exact prefixLift 654953
  have htrace : WordTrace (prefixWord ++ tailWord_654953) baseStart_654953 baseEnd_654953 := by
    simpa [prefixWord, tailWord_654953, baseEnd_654953] using wordTrace_append hprefix tailTrace_654953
  have hstable : (prefixWord ++ tailWord_654953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_654953).length < 2 ^ (prefixWord ++ tailWord_654953).sum := by decide
  have hdescent : baseEnd_654953 < baseStart_654953 := by decide
  rcases family_descends (prefixWord ++ tailWord_654953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655077 : List Nat := [1, 3, 1, 4, 1, 1, 5, 1, 4]
def baseStart_655077 : Nat := 118140960795 + 655077 * 2 ^ 59
def prefixEnd_655077 : Nat := 4983230072969 + 3 ^ 40 * 655077 * 2
def baseEnd_655077 : Nat := 149497496313528329744383

theorem tailTrace_655077 : CollatzResearch.WordTrace tailWord_655077 prefixEnd_655077 149497496313528329744383 := by
  unfold tailWord_655077
  simp only [CollatzResearch.WordTrace]
  refine ⟨23892621047775382089627485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15928414031850254726418323 23892621047775382089627485)
  ·
    refine ⟨8959732892915768283610307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23892621047775382089627485 8959732892915768283610307)
    ·
      refine ⟨13439599339373652425415461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8959732892915768283610307 13439599339373652425415461)
      ·
        refine ⟨2519924876132559829765399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13439599339373652425415461 2519924876132559829765399)
        ·
          refine ⟨3779887314198839744648099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2519924876132559829765399 3779887314198839744648099)
          ·
            refine ⟨5669830971298259616972149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3779887314198839744648099 5669830971298259616972149)
            ·
              refine ⟨531546653559211839091139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5669830971298259616972149 531546653559211839091139)
              ·
                refine ⟨797319980338817758636709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531546653559211839091139 797319980338817758636709)
                ·
                  refine ⟨149497496313528329744383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797319980338817758636709 149497496313528329744383)
                  ·
                    rfl

theorem cell21_655077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_655077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655077 prefixEnd_655077 := by exact prefixLift 655077
  have htrace : WordTrace (prefixWord ++ tailWord_655077) baseStart_655077 baseEnd_655077 := by
    simpa [prefixWord, tailWord_655077, baseEnd_655077] using wordTrace_append hprefix tailTrace_655077
  have hstable : (prefixWord ++ tailWord_655077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655077).length < 2 ^ (prefixWord ++ tailWord_655077).sum := by decide
  have hdescent : baseEnd_655077 < baseStart_655077 := by decide
  rcases family_descends (prefixWord ++ tailWord_655077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655088 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 7]
def baseStart_655088 : Nat := 118140960795 + 655088 * 2 ^ 59
def prefixEnd_655088 : Nat := 4983230072969 + 3 ^ 40 * 655088 * 2
def baseEnd_655088 : Nat := 149500006663394755061027

theorem tailTrace_655088 : CollatzResearch.WordTrace tailWord_655088 prefixEnd_655088 149500006663394755061027 := by
  unfold tailWord_655088
  simp only [CollatzResearch.WordTrace]
  refine ⟨11946511125367765484138959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15928681500490353978851945 11946511125367765484138959)
  ·
    refine ⟨17919766688051648226208439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11946511125367765484138959 17919766688051648226208439)
    ·
      refine ⟨26879650032077472339312659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17919766688051648226208439 26879650032077472339312659)
      ·
        refine ⟨40319475048116208508968989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26879650032077472339312659 40319475048116208508968989)
        ·
          refine ⟨15119803143043578190863371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40319475048116208508968989 15119803143043578190863371)
          ·
            refine ⟨22679704714565367286295057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15119803143043578190863371 22679704714565367286295057)
            ·
              refine ⟨17009778535924025464721293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22679704714565367286295057 17009778535924025464721293)
              ·
                refine ⟨6378666950971509549270485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17009778535924025464721293 6378666950971509549270485)
                ·
                  refine ⟨149500006663394755061027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6378666950971509549270485 149500006663394755061027)
                  ·
                    rfl

theorem cell21_655088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_655088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655088 prefixEnd_655088 := by exact prefixLift 655088
  have htrace : WordTrace (prefixWord ++ tailWord_655088) baseStart_655088 baseEnd_655088 := by
    simpa [prefixWord, tailWord_655088, baseEnd_655088] using wordTrace_append hprefix tailTrace_655088
  have hstable : (prefixWord ++ tailWord_655088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655088).length < 2 ^ (prefixWord ++ tailWord_655088).sum := by decide
  have hdescent : baseEnd_655088 < baseStart_655088 := by decide
  rcases family_descends (prefixWord ++ tailWord_655088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655136 : List Nat := [2, 1, 1, 5, 1, 1, 3, 3, 4]
def baseStart_655136 : Nat := 118140960795 + 655136 * 2 ^ 59
def prefixEnd_655136 : Nat := 4983230072969 + 3 ^ 40 * 655136 * 2
def baseEnd_655136 : Nat := 149510960917357338260929

theorem tailTrace_655136 : CollatzResearch.WordTrace tailWord_655136 prefixEnd_655136 149510960917357338260929 := by
  unfold tailWord_655136
  simp only [CollatzResearch.WordTrace]
  refine ⟨11947386477280817583012631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15929848636374423444016841 11947386477280817583012631)
  ·
    refine ⟨17921079715921226374518947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11947386477280817583012631 17921079715921226374518947)
    ·
      refine ⟨26881619573881839561778421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17921079715921226374518947 26881619573881839561778421)
      ·
        refine ⟨2520151835051422458916727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26881619573881839561778421 2520151835051422458916727)
        ·
          refine ⟨3780227752577133688375091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2520151835051422458916727 3780227752577133688375091)
          ·
            refine ⟨5670341628865700532562637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3780227752577133688375091 5670341628865700532562637)
            ·
              refine ⟨2126378110824637699710989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5670341628865700532562637 2126378110824637699710989)
              ·
                refine ⟨797391791559239137391621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2126378110824637699710989 797391791559239137391621)
                ·
                  refine ⟨149510960917357338260929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797391791559239137391621 149510960917357338260929)
                  ·
                    rfl

theorem cell21_655136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_655136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655136 prefixEnd_655136 := by exact prefixLift 655136
  have htrace : WordTrace (prefixWord ++ tailWord_655136) baseStart_655136 baseEnd_655136 := by
    simpa [prefixWord, tailWord_655136, baseEnd_655136] using wordTrace_append hprefix tailTrace_655136
  have hstable : (prefixWord ++ tailWord_655136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655136).length < 2 ^ (prefixWord ++ tailWord_655136).sum := by decide
  have hdescent : baseEnd_655136 < baseStart_655136 := by decide
  rcases family_descends (prefixWord ++ tailWord_655136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655209 : List Nat := [1, 2, 1, 1, 1, 3, 1, 11]
def baseStart_655209 : Nat := 118140960795 + 655209 * 2 ^ 59
def prefixEnd_655209 : Nat := 4983230072969 + 3 ^ 40 * 655209 * 2
def baseEnd_655209 : Nat := 49842540170641811181371

theorem tailTrace_655209 : CollatzResearch.WordTrace tailWord_655209 prefixEnd_655209 49842540170641811181371 := by
  unfold tailWord_655209
  simp only [CollatzResearch.WordTrace]
  refine ⟨23897435483297168633432681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15931623655531445755621787 23897435483297168633432681)
  ·
    refine ⟨17923076612472876475074511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23897435483297168633432681 17923076612472876475074511)
    ·
      refine ⟨26884614918709314712611767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17923076612472876475074511 26884614918709314712611767)
      ·
        refine ⟨40326922378063972068917651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26884614918709314712611767 40326922378063972068917651)
        ·
          refine ⟨60490383567095958103376477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40326922378063972068917651 60490383567095958103376477)
          ·
            refine ⟨22683893837660984288766179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60490383567095958103376477 22683893837660984288766179)
            ·
              refine ⟨34025840756491476433149269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22683893837660984288766179 34025840756491476433149269)
              ·
                refine ⟨49842540170641811181371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 34025840756491476433149269 49842540170641811181371)
                ·
                  rfl

theorem cell21_655209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 11].length) (baseStart_655209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655209 prefixEnd_655209 := by exact prefixLift 655209
  have htrace : WordTrace (prefixWord ++ tailWord_655209) baseStart_655209 baseEnd_655209 := by
    simpa [prefixWord, tailWord_655209, baseEnd_655209] using wordTrace_append hprefix tailTrace_655209
  have hstable : (prefixWord ++ tailWord_655209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655209).length < 2 ^ (prefixWord ++ tailWord_655209).sum := by decide
  have hdescent : baseEnd_655209 < baseStart_655209 := by decide
  rcases family_descends (prefixWord ++ tailWord_655209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655260 : List Nat := [2, 2, 3, 3, 1, 3, 2, 5]
def baseStart_655260 : Nat := 118140960795 + 655260 * 2 ^ 59
def prefixEnd_655260 : Nat := 4983230072969 + 3 ^ 40 * 655260 * 2
def baseEnd_655260 : Nat := 49846419802253559398003

theorem tailTrace_655260 : CollatzResearch.WordTrace tailWord_655260 prefixEnd_655260 49846419802253559398003 := by
  unfold tailWord_655260
  simp only [CollatzResearch.WordTrace]
  refine ⟨11949647803056202171769617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15932863737408269562359489 11949647803056202171769617)
  ·
    refine ⟨8962235852292151628827213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11949647803056202171769617 8962235852292151628827213)
    ·
      refine ⟨3360838444609556860810205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8962235852292151628827213 3360838444609556860810205)
      ·
        refine ⟨1260314416728583822803827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3360838444609556860810205 1260314416728583822803827)
        ·
          refine ⟨1890471625092875734205741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1260314416728583822803827 1890471625092875734205741)
          ·
            refine ⟨708926859409828400327153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1890471625092875734205741 708926859409828400327153)
            ·
              refine ⟨531695144557371300245365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708926859409828400327153 531695144557371300245365)
              ·
                refine ⟨49846419802253559398003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 531695144557371300245365 49846419802253559398003)
                ·
                  rfl

theorem cell21_655260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 5].length) (baseStart_655260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655260 prefixEnd_655260 := by exact prefixLift 655260
  have htrace : WordTrace (prefixWord ++ tailWord_655260) baseStart_655260 baseEnd_655260 := by
    simpa [prefixWord, tailWord_655260, baseEnd_655260] using wordTrace_append hprefix tailTrace_655260
  have hstable : (prefixWord ++ tailWord_655260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655260).length < 2 ^ (prefixWord ++ tailWord_655260).sum := by decide
  have hdescent : baseEnd_655260 < baseStart_655260 := by decide
  rcases family_descends (prefixWord ++ tailWord_655260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655409 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 5]
def baseStart_655409 : Nat := 118140960795 + 655409 * 2 ^ 59
def prefixEnd_655409 : Nat := 4983230072969 + 3 ^ 40 * 655409 * 2
def baseEnd_655409 : Nat := 149573263236769530210371

theorem tailTrace_655409 : CollatzResearch.WordTrace tailWord_655409 prefixEnd_655409 149573263236769530210371 := by
  unfold tailWord_655409
  simp only [CollatzResearch.WordTrace]
  refine ⟨23904730082572602790713281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15936486721715068527142187 23904730082572602790713281)
  ·
    refine ⟨17928547561929452093034961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23904730082572602790713281 17928547561929452093034961)
    ·
      refine ⟨13446410671447089069776221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17928547561929452093034961 13446410671447089069776221)
      ·
        refine ⟨5042404001792658401166083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13446410671447089069776221 5042404001792658401166083)
        ·
          refine ⟨7563606002688987601749125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5042404001792658401166083 7563606002688987601749125)
          ·
            refine ⟨1418176125504185175327961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7563606002688987601749125 1418176125504185175327961)
            ·
              refine ⟨1063632094128138881495971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1418176125504185175327961 1063632094128138881495971)
              ·
                refine ⟨1595448141192208322243957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1063632094128138881495971 1595448141192208322243957)
                ·
                  refine ⟨149573263236769530210371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1595448141192208322243957 149573263236769530210371)
                  ·
                    rfl

theorem cell21_655409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_655409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655409 prefixEnd_655409 := by exact prefixLift 655409
  have htrace : WordTrace (prefixWord ++ tailWord_655409) baseStart_655409 baseEnd_655409 := by
    simpa [prefixWord, tailWord_655409, baseEnd_655409] using wordTrace_append hprefix tailTrace_655409
  have hstable : (prefixWord ++ tailWord_655409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655409).length < 2 ^ (prefixWord ++ tailWord_655409).sum := by decide
  have hdescent : baseEnd_655409 < baseStart_655409 := by decide
  rcases family_descends (prefixWord ++ tailWord_655409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655423 : List Nat := [1, 1, 2, 2, 3, 1, 2, 5, 4]
def baseStart_655423 : Nat := 118140960795 + 655423 * 2 ^ 59
def prefixEnd_655423 : Nat := 4983230072969 + 3 ^ 40 * 655423 * 2
def baseEnd_655423 : Nat := 149576458227508616977009

theorem tailTrace_655423 : CollatzResearch.WordTrace tailWord_655423 prefixEnd_655423 149576458227508616977009 := by
  unfold tailWord_655423
  simp only [CollatzResearch.WordTrace]
  refine ⟨23905240704521883181722923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15936827136347922121148615 23905240704521883181722923)
  ·
    refine ⟨35857861056782824772584385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23905240704521883181722923 35857861056782824772584385)
    ·
      refine ⟨26893395792587118579438289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35857861056782824772584385 26893395792587118579438289)
      ·
        refine ⟨20170046844440338934578717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26893395792587118579438289 20170046844440338934578717)
        ·
          refine ⟨7563767566665127100467019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20170046844440338934578717 7563767566665127100467019)
          ·
            refine ⟨11345651349997690650700529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7563767566665127100467019 11345651349997690650700529)
            ·
              refine ⟨8509238512498267988025397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11345651349997690650700529 8509238512498267988025397)
              ·
                refine ⟨797741110546712623877381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8509238512498267988025397 797741110546712623877381)
                ·
                  refine ⟨149576458227508616977009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797741110546712623877381 149576458227508616977009)
                  ·
                    rfl

theorem cell21_655423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 4].length) (baseStart_655423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655423 prefixEnd_655423 := by exact prefixLift 655423
  have htrace : WordTrace (prefixWord ++ tailWord_655423) baseStart_655423 baseEnd_655423 := by
    simpa [prefixWord, tailWord_655423, baseEnd_655423] using wordTrace_append hprefix tailTrace_655423
  have hstable : (prefixWord ++ tailWord_655423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655423).length < 2 ^ (prefixWord ++ tailWord_655423).sum := by decide
  have hdescent : baseEnd_655423 < baseStart_655423 := by decide
  rcases family_descends (prefixWord ++ tailWord_655423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655516 : List Nat := [2, 2, 3, 2, 1, 1, 4, 2, 4]
def baseStart_655516 : Nat := 118140960795 + 655516 * 2 ^ 59
def prefixEnd_655516 : Nat := 4983230072969 + 3 ^ 40 * 655516 * 2
def baseEnd_655516 : Nat := 149597682094561121926819

theorem tailTrace_655516 : CollatzResearch.WordTrace tailWord_655516 prefixEnd_655516 149597682094561121926819 := by
  unfold tailWord_655516
  simp only [CollatzResearch.WordTrace]
  refine ⟨11954316346592480032429201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15939088462123306709905601 11954316346592480032429201)
  ·
    refine ⟨8965737259944360024321901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11954316346592480032429201 8965737259944360024321901)
    ·
      refine ⟨3362151472479135009120713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8965737259944360024321901 3362151472479135009120713)
      ·
        refine ⟨2521613604359351256840535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3362151472479135009120713 2521613604359351256840535)
        ·
          refine ⟨3782420406539026885260803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2521613604359351256840535 3782420406539026885260803)
          ·
            refine ⟨5673630609808540327891205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3782420406539026885260803 5673630609808540327891205)
            ·
              refine ⟨1063805739339101311479601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5673630609808540327891205 1063805739339101311479601)
              ·
                refine ⟨797854304504325983609701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1063805739339101311479601 797854304504325983609701)
                ·
                  refine ⟨149597682094561121926819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797854304504325983609701 149597682094561121926819)
                  ·
                    rfl

theorem cell21_655516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_655516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655516 prefixEnd_655516 := by exact prefixLift 655516
  have htrace : WordTrace (prefixWord ++ tailWord_655516) baseStart_655516 baseEnd_655516 := by
    simpa [prefixWord, tailWord_655516, baseEnd_655516] using wordTrace_append hprefix tailTrace_655516
  have hstable : (prefixWord ++ tailWord_655516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655516).length < 2 ^ (prefixWord ++ tailWord_655516).sum := by decide
  have hdescent : baseEnd_655516 < baseStart_655516 := by decide
  rcases family_descends (prefixWord ++ tailWord_655516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655519 : List Nat := [1, 1, 2, 6, 1, 1, 4, 2, 3]
def baseStart_655519 : Nat := 118140960795 + 655519 * 2 ^ 59
def prefixEnd_655519 : Nat := 4983230072969 + 3 ^ 40 * 655519 * 2
def baseEnd_655519 : Nat := 149598366735433783376813

theorem tailTrace_655519 : CollatzResearch.WordTrace tailWord_655519 prefixEnd_655519 149598366735433783376813 := by
  unfold tailWord_655519
  simp only [CollatzResearch.WordTrace]
  refine ⟨23908742112174091577217611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15939161408116061051478407 23908742112174091577217611)
  ·
    refine ⟨35863113168261137365826417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23908742112174091577217611 35863113168261137365826417)
    ·
      refine ⟨26897334876195853024369813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35863113168261137365826417 26897334876195853024369813)
      ·
        refine ⟨1260812572321680610517335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26897334876195853024369813 1260812572321680610517335)
        ·
          refine ⟨1891218858482520915776003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1260812572321680610517335 1891218858482520915776003)
          ·
            refine ⟨2836828287723781373664005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891218858482520915776003 2836828287723781373664005)
            ·
              refine ⟨531905303948209007562001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2836828287723781373664005 531905303948209007562001)
              ·
                refine ⟨398928977961156755671501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531905303948209007562001 398928977961156755671501)
                ·
                  refine ⟨149598366735433783376813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398928977961156755671501 149598366735433783376813)
                  ·
                    rfl

theorem cell21_655519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 3].length) (baseStart_655519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655519 prefixEnd_655519 := by exact prefixLift 655519
  have htrace : WordTrace (prefixWord ++ tailWord_655519) baseStart_655519 baseEnd_655519 := by
    simpa [prefixWord, tailWord_655519, baseEnd_655519] using wordTrace_append hprefix tailTrace_655519
  have hstable : (prefixWord ++ tailWord_655519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655519).length < 2 ^ (prefixWord ++ tailWord_655519).sum := by decide
  have hdescent : baseEnd_655519 < baseStart_655519 := by decide
  rcases family_descends (prefixWord ++ tailWord_655519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655544 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 5]
def baseStart_655544 : Nat := 118140960795 + 655544 * 2 ^ 59
def prefixEnd_655544 : Nat := 4983230072969 + 3 ^ 40 * 655544 * 2
def baseEnd_655544 : Nat := 149604072076039295460095

theorem tailTrace_655544 : CollatzResearch.WordTrace tailWord_655544 prefixEnd_655544 149604072076039295460095 := by
  unfold tailWord_655544
  simp only [CollatzResearch.WordTrace]
  refine ⟨11954826968541760423438843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15939769291389013897918457 11954826968541760423438843)
  ·
    refine ⟨17932240452812640635158265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11954826968541760423438843 17932240452812640635158265)
    ·
      refine ⟨13449180339609480476368699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17932240452812640635158265 13449180339609480476368699)
      ·
        refine ⟨20173770509414220714553049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13449180339609480476368699 20173770509414220714553049)
        ·
          refine ⟨15130327882060665535914787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20173770509414220714553049 15130327882060665535914787)
          ·
            refine ⟨22695491823090998303872181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15130327882060665535914787 22695491823090998303872181)
            ·
              refine ⟨2127702358414781090988017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22695491823090998303872181 2127702358414781090988017)
              ·
                refine ⟨1595776768811085818241013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2127702358414781090988017 1595776768811085818241013)
                ·
                  refine ⟨149604072076039295460095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1595776768811085818241013 149604072076039295460095)
                  ·
                    rfl

theorem cell21_655544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_655544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655544 prefixEnd_655544 := by exact prefixLift 655544
  have htrace : WordTrace (prefixWord ++ tailWord_655544) baseStart_655544 baseEnd_655544 := by
    simpa [prefixWord, tailWord_655544, baseEnd_655544] using wordTrace_append hprefix tailTrace_655544
  have hstable : (prefixWord ++ tailWord_655544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655544).length < 2 ^ (prefixWord ++ tailWord_655544).sum := by decide
  have hdescent : baseEnd_655544 < baseStart_655544 := by decide
  rcases family_descends (prefixWord ++ tailWord_655544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655623 : List Nat := [1, 1, 4, 5, 1, 2, 7]
def baseStart_655623 : Nat := 118140960795 + 655623 * 2 ^ 59
def prefixEnd_655623 : Nat := 4983230072969 + 3 ^ 40 * 655623 * 2
def baseEnd_655623 : Nat := 16624677883594745960363

theorem tailTrace_655623 : CollatzResearch.WordTrace tailWord_655623 prefixEnd_655623 16624677883594745960363 := by
  unfold tailWord_655623
  simp only [CollatzResearch.WordTrace]
  refine ⟨23912535303797317339003523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15941690202531544892669015 23912535303797317339003523)
  ·
    refine ⟨35868802955695976008505285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23912535303797317339003523 35868802955695976008505285)
    ·
      refine ⟨6725400554192995501594741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35868802955695976008505285 6725400554192995501594741)
      ·
        refine ⟨630506301955593328274507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6725400554192995501594741 630506301955593328274507)
        ·
          refine ⟨945759452933389992411761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630506301955593328274507 945759452933389992411761)
          ·
            refine ⟨709319589700042494308821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 945759452933389992411761 709319589700042494308821)
            ·
              refine ⟨16624677883594745960363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 709319589700042494308821 16624677883594745960363)
              ·
                rfl

theorem cell21_655623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 7].length) (baseStart_655623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655623 prefixEnd_655623 := by exact prefixLift 655623
  have htrace : WordTrace (prefixWord ++ tailWord_655623) baseStart_655623 baseEnd_655623 := by
    simpa [prefixWord, tailWord_655623, baseEnd_655623] using wordTrace_append hprefix tailTrace_655623
  have hstable : (prefixWord ++ tailWord_655623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655623).length < 2 ^ (prefixWord ++ tailWord_655623).sum := by decide
  have hdescent : baseEnd_655623 < baseStart_655623 := by decide
  rcases family_descends (prefixWord ++ tailWord_655623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655637 : List Nat := [1, 3, 2, 1, 2, 1, 2, 6, 3]
def baseStart_655637 : Nat := 118140960795 + 655637 * 2 ^ 59
def prefixEnd_655637 : Nat := 4983230072969 + 3 ^ 40 * 655637 * 2
def baseEnd_655637 : Nat := 149625295943091800409905

theorem tailTrace_655637 : CollatzResearch.WordTrace tailWord_655637 prefixEnd_655637 149625295943091800409905 := by
  unfold tailWord_655637
  simp only [CollatzResearch.WordTrace]
  refine ⟨23913045925746597730013165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15942030617164398486675443 23913045925746597730013165)
  ·
    refine ⟨8967392222154974148754937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23913045925746597730013165 8967392222154974148754937)
    ·
      refine ⟨6725544166616230611566203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8967392222154974148754937 6725544166616230611566203)
      ·
        refine ⟨10088316249924345917349305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6725544166616230611566203 10088316249924345917349305)
        ·
          refine ⟨7566237187443259438011979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10088316249924345917349305 7566237187443259438011979)
          ·
            refine ⟨11349355781164889157017969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7566237187443259438011979 11349355781164889157017969)
            ·
              refine ⟨8512016835873666867763477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11349355781164889157017969 8512016835873666867763477)
              ·
                refine ⟨399000789181578134426413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8512016835873666867763477 399000789181578134426413)
                ·
                  refine ⟨149625295943091800409905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399000789181578134426413 149625295943091800409905)
                  ·
                    rfl

theorem cell21_655637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_655637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655637 prefixEnd_655637 := by exact prefixLift 655637
  have htrace : WordTrace (prefixWord ++ tailWord_655637) baseStart_655637 baseEnd_655637 := by
    simpa [prefixWord, tailWord_655637, baseEnd_655637] using wordTrace_append hprefix tailTrace_655637
  have hstable : (prefixWord ++ tailWord_655637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655637).length < 2 ^ (prefixWord ++ tailWord_655637).sum := by decide
  have hdescent : baseEnd_655637 < baseStart_655637 := by decide
  rcases family_descends (prefixWord ++ tailWord_655637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655651 : List Nat := [1, 1, 1, 4, 2, 2, 3, 3, 4]
def baseStart_655651 : Nat := 118140960795 + 655651 * 2 ^ 59
def prefixEnd_655651 : Nat := 4983230072969 + 3 ^ 40 * 655651 * 2
def baseEnd_655651 : Nat := 149628490933830887176543

theorem tailTrace_655651 : CollatzResearch.WordTrace tailWord_655651 prefixEnd_655651 149628490933830887176543 := by
  unfold tailWord_655651
  simp only [CollatzResearch.WordTrace]
  refine ⟨23913556547695878121022807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15942371031797252080681871 23913556547695878121022807)
  ·
    refine ⟨35870334821543817181534211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23913556547695878121022807 35870334821543817181534211)
    ·
      refine ⟨53805502232315725772301317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35870334821543817181534211 53805502232315725772301317)
      ·
        refine ⟨10088531668559198582306497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53805502232315725772301317 10088531668559198582306497)
        ·
          refine ⟨7566398751419398936729873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10088531668559198582306497 7566398751419398936729873)
          ·
            refine ⟨5674799063564549202547405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7566398751419398936729873 5674799063564549202547405)
            ·
              refine ⟨2128049648836705950955277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5674799063564549202547405 2128049648836705950955277)
              ·
                refine ⟨798018618313764731608229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2128049648836705950955277 798018618313764731608229)
                ·
                  refine ⟨149628490933830887176543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 798018618313764731608229 149628490933830887176543)
                  ·
                    rfl

theorem cell21_655651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 4].length) (baseStart_655651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655651 prefixEnd_655651 := by exact prefixLift 655651
  have htrace : WordTrace (prefixWord ++ tailWord_655651) baseStart_655651 baseEnd_655651 := by
    simpa [prefixWord, tailWord_655651, baseEnd_655651] using wordTrace_append hprefix tailTrace_655651
  have hstable : (prefixWord ++ tailWord_655651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655651).length < 2 ^ (prefixWord ++ tailWord_655651).sum := by decide
  have hdescent : baseEnd_655651 < baseStart_655651 := by decide
  rcases family_descends (prefixWord ++ tailWord_655651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655730 : List Nat := [3, 2, 1, 2, 1, 4, 2, 3, 3]
def baseStart_655730 : Nat := 118140960795 + 655730 * 2 ^ 59
def prefixEnd_655730 : Nat := 4983230072969 + 3 ^ 40 * 655730 * 2
def baseEnd_655730 : Nat := 149646519810144305359715

theorem tailTrace_655730 : CollatzResearch.WordTrace tailWord_655730 prefixEnd_655730 149646519810144305359715 := by
  unfold tailWord_655730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5979109478602418653287161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15944291942939783075432429 5979109478602418653287161)
  ·
    refine ⟨4484332108951813989965371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5979109478602418653287161 4484332108951813989965371)
    ·
      refine ⟨6726498163427720984948057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4484332108951813989965371 6726498163427720984948057)
      ·
        refine ⟨5044873622570790738711043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6726498163427720984948057 5044873622570790738711043)
        ·
          refine ⟨7567310433856186108066565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5044873622570790738711043 7567310433856186108066565)
          ·
            refine ⟨1418870706348034895262481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7567310433856186108066565 1418870706348034895262481)
            ·
              refine ⟨1064153029761026171446861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1418870706348034895262481 1064153029761026171446861)
              ·
                refine ⟨399057386160384814292573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1064153029761026171446861 399057386160384814292573)
                ·
                  refine ⟨149646519810144305359715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399057386160384814292573 149646519810144305359715)
                  ·
                    rfl

theorem cell21_655730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_655730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655730 prefixEnd_655730 := by exact prefixLift 655730
  have htrace : WordTrace (prefixWord ++ tailWord_655730) baseStart_655730 baseEnd_655730 := by
    simpa [prefixWord, tailWord_655730, baseEnd_655730] using wordTrace_append hprefix tailTrace_655730
  have hstable : (prefixWord ++ tailWord_655730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655730).length < 2 ^ (prefixWord ++ tailWord_655730).sum := by decide
  have hdescent : baseEnd_655730 < baseStart_655730 := by decide
  rcases family_descends (prefixWord ++ tailWord_655730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655741 : List Nat := [1, 4, 1, 1, 2, 4, 8]
def baseStart_655741 : Nat := 118140960795 + 655741 * 2 ^ 59
def prefixEnd_655741 : Nat := 4983230072969 + 3 ^ 40 * 655741 * 2
def baseEnd_655741 : Nat := 16627670017778970075151

theorem tailTrace_655741 : CollatzResearch.WordTrace tailWord_655741 prefixEnd_655741 16627670017778970075151 := by
  unfold tailWord_655741
  simp only [CollatzResearch.WordTrace]
  refine ⟨23916839117369823491799077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15944559411579882327866051 23916839117369823491799077)
  ·
    refine ⟨4484407334506841904712327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23916839117369823491799077 4484407334506841904712327)
    ·
      refine ⟨6726611001760262857068491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4484407334506841904712327 6726611001760262857068491)
      ·
        refine ⟨10089916502640394285602737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6726611001760262857068491 10089916502640394285602737)
        ·
          refine ⟨7567437376980295714202053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10089916502640394285602737 7567437376980295714202053)
          ·
            refine ⟨1418894508183805446412885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7567437376980295714202053 1418894508183805446412885)
            ·
              refine ⟨16627670017778970075151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1418894508183805446412885 16627670017778970075151)
              ·
                rfl

theorem cell21_655741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 8].length) (baseStart_655741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655741 prefixEnd_655741 := by exact prefixLift 655741
  have htrace : WordTrace (prefixWord ++ tailWord_655741) baseStart_655741 baseEnd_655741 := by
    simpa [prefixWord, tailWord_655741, baseEnd_655741] using wordTrace_append hprefix tailTrace_655741
  have hstable : (prefixWord ++ tailWord_655741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655741).length < 2 ^ (prefixWord ++ tailWord_655741).sum := by decide
  have hdescent : baseEnd_655741 < baseStart_655741 := by decide
  rcases family_descends (prefixWord ++ tailWord_655741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655820 : List Nat := [2, 2, 1, 4, 3, 1, 1, 3, 4]
def baseStart_655820 : Nat := 118140960795 + 655820 * 2 ^ 59
def prefixEnd_655820 : Nat := 4983230072969 + 3 ^ 40 * 655820 * 2
def baseEnd_655820 : Nat := 149667059036324148859531

theorem tailTrace_655820 : CollatzResearch.WordTrace tailWord_655820 prefixEnd_655820 149667059036324148859531 := by
  unfold tailWord_655820
  simp only [CollatzResearch.WordTrace]
  refine ⟨11959860242041809991962457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15946480322722413322616609 11959860242041809991962457)
  ·
    refine ⟨8969895181531357493971843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11959860242041809991962457 8969895181531357493971843)
    ·
      refine ⟨13454842772297036240957765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8969895181531357493971843 13454842772297036240957765)
      ·
        refine ⟨2522783019805694295179581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13454842772297036240957765 2522783019805694295179581)
        ·
          refine ⟨946043632427135360692343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2522783019805694295179581 946043632427135360692343)
          ·
            refine ⟨1419065448640703041038515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946043632427135360692343 1419065448640703041038515)
            ·
              refine ⟨2128598172961054561557773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419065448640703041038515 2128598172961054561557773)
              ·
                refine ⟨798224314860395460584165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2128598172961054561557773 798224314860395460584165)
                ·
                  refine ⟨149667059036324148859531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 798224314860395460584165 149667059036324148859531)
                  ·
                    rfl

theorem cell21_655820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_655820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655820 prefixEnd_655820 := by exact prefixLift 655820
  have htrace : WordTrace (prefixWord ++ tailWord_655820) baseStart_655820 baseEnd_655820 := by
    simpa [prefixWord, tailWord_655820, baseEnd_655820] using wordTrace_append hprefix tailTrace_655820
  have hstable : (prefixWord ++ tailWord_655820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655820).length < 2 ^ (prefixWord ++ tailWord_655820).sum := by decide
  have hdescent : baseEnd_655820 < baseStart_655820 := by decide
  rcases family_descends (prefixWord ++ tailWord_655820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655969 : List Nat := [1, 2, 3, 1, 1, 6, 7]
def baseStart_655969 : Nat := 118140960795 + 655969 * 2 ^ 59
def prefixEnd_655969 : Nat := 4983230072969 + 3 ^ 40 * 655969 * 2
def baseEnd_655969 : Nat := 16633451429592555652877

theorem tailTrace_655969 : CollatzResearch.WordTrace tailWord_655969 prefixEnd_655969 16633451429592555652877 := by
  unfold tailWord_655969
  simp only [CollatzResearch.WordTrace]
  refine ⟨23925154960543818431098961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15950103307029212287399307 23925154960543818431098961)
  ·
    refine ⟨17943866220407863823324221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23925154960543818431098961 17943866220407863823324221)
    ·
      refine ⟨6728949832652948933746583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17943866220407863823324221 6728949832652948933746583)
      ·
        refine ⟨10093424748979423400619875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6728949832652948933746583 10093424748979423400619875)
        ·
          refine ⟨15140137123469135100929813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10093424748979423400619875 15140137123469135100929813)
          ·
            refine ⟨709693927662615707856085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15140137123469135100929813 709693927662615707856085)
            ·
              refine ⟨16633451429592555652877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 709693927662615707856085 16633451429592555652877)
              ·
                rfl

theorem cell21_655969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 7].length) (baseStart_655969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655969 prefixEnd_655969 := by exact prefixLift 655969
  have htrace : WordTrace (prefixWord ++ tailWord_655969) baseStart_655969 baseEnd_655969 := by
    simpa [prefixWord, tailWord_655969, baseEnd_655969] using wordTrace_append hprefix tailTrace_655969
  have hstable : (prefixWord ++ tailWord_655969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655969).length < 2 ^ (prefixWord ++ tailWord_655969).sum := by decide
  have hdescent : baseEnd_655969 < baseStart_655969 := by decide
  rcases family_descends (prefixWord ++ tailWord_655969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655986 : List Nat := [3, 2, 1, 2, 4, 1, 2, 6]
def baseStart_655986 : Nat := 118140960795 + 655986 * 2 ^ 59
def prefixEnd_655986 : Nat := 4983230072969 + 3 ^ 40 * 655986 * 2
def baseEnd_655986 : Nat := 49901647499314916364175

theorem tailTrace_655986 : CollatzResearch.WordTrace tailWord_655986 prefixEnd_655986 49901647499314916364175 := by
  unfold tailWord_655986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5981443750370557583616953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15950516667654820222978541 5981443750370557583616953)
  ·
    refine ⟨4486082812777918187712715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5981443750370557583616953 4486082812777918187712715)
    ·
      refine ⟨6729124219166877281569073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4486082812777918187712715 6729124219166877281569073)
      ·
        refine ⟨5046843164375157961176805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6729124219166877281569073 5046843164375157961176805)
        ·
          refine ⟨946283093320342117720651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5046843164375157961176805 946283093320342117720651)
          ·
            refine ⟨1419424639980513176580977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946283093320342117720651 1419424639980513176580977)
            ·
              refine ⟨1064568479985384882435733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1419424639980513176580977 1064568479985384882435733)
              ·
                refine ⟨49901647499314916364175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1064568479985384882435733 49901647499314916364175)
                ·
                  rfl

theorem cell21_655986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_655986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_655986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_655986 prefixEnd_655986 := by exact prefixLift 655986
  have htrace : WordTrace (prefixWord ++ tailWord_655986) baseStart_655986 baseEnd_655986 := by
    simpa [prefixWord, tailWord_655986, baseEnd_655986] using wordTrace_append hprefix tailTrace_655986
  have hstable : (prefixWord ++ tailWord_655986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655986).length < 2 ^ (prefixWord ++ tailWord_655986).sum := by decide
  have hdescent : baseEnd_655986 < baseStart_655986 := by decide
  rcases family_descends (prefixWord ++ tailWord_655986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656062 : List Nat := [4, 2, 1, 1, 2, 1, 5, 5]
def baseStart_656062 : Nat := 118140960795 + 656062 * 2 ^ 59
def prefixEnd_656062 : Nat := 4983230072969 + 3 ^ 40 * 656062 * 2
def baseEnd_656062 : Nat := 49907428911128501941901

theorem tailTrace_656062 : CollatzResearch.WordTrace tailWord_656062 prefixEnd_656062 49907428911128501941901 := by
  unfold tailWord_656062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2991068368650861914279305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15952364632804596876156293 2991068368650861914279305)
  ·
    refine ⟨2243301276488146435709479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2991068368650861914279305 2243301276488146435709479)
    ·
      refine ⟨3364951914732219653564219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2243301276488146435709479 3364951914732219653564219)
      ·
        refine ⟨5047427872098329480346329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3364951914732219653564219 5047427872098329480346329)
        ·
          refine ⟨3785570904073747110259747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5047427872098329480346329 3785570904073747110259747)
          ·
            refine ⟨5678356356110620665389621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3785570904073747110259747 5678356356110620665389621)
            ·
              refine ⟨532345908385370687380277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5678356356110620665389621 532345908385370687380277)
              ·
                refine ⟨49907428911128501941901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 532345908385370687380277 49907428911128501941901)
                ·
                  rfl

theorem cell21_656062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_656062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656062 prefixEnd_656062 := by exact prefixLift 656062
  have htrace : WordTrace (prefixWord ++ tailWord_656062) baseStart_656062 baseEnd_656062 := by
    simpa [prefixWord, tailWord_656062, baseEnd_656062] using wordTrace_append hprefix tailTrace_656062
  have hstable : (prefixWord ++ tailWord_656062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656062).length < 2 ^ (prefixWord ++ tailWord_656062).sum := by decide
  have hdescent : baseEnd_656062 < baseStart_656062 := by decide
  rcases family_descends (prefixWord ++ tailWord_656062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656090 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_656090 : Nat := 118140960795 + 656090 * 2 ^ 59
def prefixEnd_656090 : Nat := 4983230072969 + 3 ^ 40 * 656090 * 2
def baseEnd_656090 : Nat := 149728676714863679358979

theorem tailTrace_656090 : CollatzResearch.WordTrace tailWord_656090 prefixEnd_656090 149728676714863679358979 := by
  unfold tailWord_656090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5982392048276364024063431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15953045462070304064169149 5982392048276364024063431)
  ·
    refine ⟨8973588072414546036095147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5982392048276364024063431 8973588072414546036095147)
    ·
      refine ⟨13460382108621819054142721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8973588072414546036095147 13460382108621819054142721)
      ·
        refine ⟨10095286581466364290607041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13460382108621819054142721 10095286581466364290607041)
        ·
          refine ⟨7571464936099773217955281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10095286581466364290607041 7571464936099773217955281)
          ·
            refine ⟨5678598702074829913466461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7571464936099773217955281 5678598702074829913466461)
            ·
              refine ⟨2129474513278061217549923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5678598702074829913466461 2129474513278061217549923)
              ·
                refine ⟨3194211769917091826324885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2129474513278061217549923 3194211769917091826324885)
                ·
                  refine ⟨149728676714863679358979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3194211769917091826324885 149728676714863679358979)
                  ·
                    rfl

theorem cell21_656090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_656090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656090 prefixEnd_656090 := by exact prefixLift 656090
  have htrace : WordTrace (prefixWord ++ tailWord_656090) baseStart_656090 baseEnd_656090 := by
    simpa [prefixWord, tailWord_656090, baseEnd_656090] using wordTrace_append hprefix tailTrace_656090
  have hstable : (prefixWord ++ tailWord_656090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656090).length < 2 ^ (prefixWord ++ tailWord_656090).sum := by decide
  have hdescent : baseEnd_656090 < baseStart_656090 := by decide
  rcases family_descends (prefixWord ++ tailWord_656090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656228 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 5]
def baseStart_656228 : Nat := 118140960795 + 656228 * 2 ^ 59
def prefixEnd_656228 : Nat := 4983230072969 + 3 ^ 40 * 656228 * 2
def baseEnd_656228 : Nat := 149760170195006106058697

theorem tailTrace_656228 : CollatzResearch.WordTrace tailWord_656228 prefixEnd_656228 149760170195006106058697 := by
  unfold tailWord_656228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11967300733302752832388669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15956400977737003776518225 11967300733302752832388669)
  ·
    refine ⟨4487737774988532312145751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11967300733302752832388669 4487737774988532312145751)
    ·
      refine ⟨6731606662482798468218627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4487737774988532312145751 6731606662482798468218627)
      ·
        refine ⟨10097409993724197702327941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6731606662482798468218627 10097409993724197702327941)
        ·
          refine ⟨1893264373823287069186489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10097409993724197702327941 1893264373823287069186489)
          ·
            refine ⟨1419948280367465301889867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1893264373823287069186489 1419948280367465301889867)
            ·
              refine ⟨2129922420551197952834801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419948280367465301889867 2129922420551197952834801)
              ·
                refine ⟨1597441815413398464626101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2129922420551197952834801 1597441815413398464626101)
                ·
                  refine ⟨149760170195006106058697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1597441815413398464626101 149760170195006106058697)
                  ·
                    rfl

theorem cell21_656228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_656228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656228 prefixEnd_656228 := by exact prefixLift 656228
  have htrace : WordTrace (prefixWord ++ tailWord_656228) baseStart_656228 baseEnd_656228 := by
    simpa [prefixWord, tailWord_656228, baseEnd_656228] using wordTrace_append hprefix tailTrace_656228
  have hstable : (prefixWord ++ tailWord_656228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656228).length < 2 ^ (prefixWord ++ tailWord_656228).sum := by decide
  have hdescent : baseEnd_656228 < baseStart_656228 := by decide
  rcases family_descends (prefixWord ++ tailWord_656228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656245 : List Nat := [1, 3, 4, 1, 1, 2, 1, 5, 3]
def baseStart_656245 : Nat := 118140960795 + 656245 * 2 ^ 59
def prefixEnd_656245 : Nat := 4983230072969 + 3 ^ 40 * 656245 * 2
def baseEnd_656245 : Nat := 149764049826617854275329

theorem tailTrace_656245 : CollatzResearch.WordTrace tailWord_656245 prefixEnd_656245 149764049826617854275329 := by
  unfold tailWord_656245
  simp only [CollatzResearch.WordTrace]
  refine ⟨23935221507543917568146189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15956814338362611712097459 23935221507543917568146189)
  ·
    refine ⟨8975708065328969088054821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23935221507543917568146189 8975708065328969088054821)
    ·
      refine ⟨1682945262249181704010279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8975708065328969088054821 1682945262249181704010279)
      ·
        refine ⟨2524417893373772556015419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1682945262249181704010279 2524417893373772556015419)
        ·
          refine ⟨3786626840060658834023129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2524417893373772556015419 3786626840060658834023129)
          ·
            refine ⟨2839970130045494125517347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3786626840060658834023129 2839970130045494125517347)
            ·
              refine ⟨4259955195068241188276021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839970130045494125517347 4259955195068241188276021)
              ·
                refine ⟨399370799537647611400877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4259955195068241188276021 399370799537647611400877)
                ·
                  refine ⟨149764049826617854275329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399370799537647611400877 149764049826617854275329)
                  ·
                    rfl

theorem cell21_656245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_656245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656245 prefixEnd_656245 := by exact prefixLift 656245
  have htrace : WordTrace (prefixWord ++ tailWord_656245) baseStart_656245 baseEnd_656245 := by
    simpa [prefixWord, tailWord_656245, baseEnd_656245] using wordTrace_append hprefix tailTrace_656245
  have hstable : (prefixWord ++ tailWord_656245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656245).length < 2 ^ (prefixWord ++ tailWord_656245).sum := by decide
  have hdescent : baseEnd_656245 < baseStart_656245 := by decide
  rcases family_descends (prefixWord ++ tailWord_656245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656276 : List Nat := [2, 4, 2, 1, 1, 1, 5, 1, 4]
def baseStart_656276 : Nat := 118140960795 + 656276 * 2 ^ 59
def prefixEnd_656276 : Nat := 4983230072969 + 3 ^ 40 * 656276 * 2
def baseEnd_656276 : Nat := 149771124448968689258599

theorem tailTrace_656276 : CollatzResearch.WordTrace tailWord_656276 prefixEnd_656276 149771124448968689258599 := by
  unfold tailWord_656276
  simp only [CollatzResearch.WordTrace]
  refine ⟨11968176085215804931262341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15957568113621073241683121 11968176085215804931262341)
  ·
    refine ⟨2244033015977963424611689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11968176085215804931262341 2244033015977963424611689)
    ·
      refine ⟨1683024761983472568458767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2244033015977963424611689 1683024761983472568458767)
      ·
        refine ⟨2524537142975208852688151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683024761983472568458767 2524537142975208852688151)
        ·
          refine ⟨3786805714462813279032227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2524537142975208852688151 3786805714462813279032227)
          ·
            refine ⟨5680208571694219918548341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3786805714462813279032227 5680208571694219918548341)
            ·
              refine ⟨532519553596333117363907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5680208571694219918548341 532519553596333117363907)
              ·
                refine ⟨798779330394499676045861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532519553596333117363907 798779330394499676045861)
                ·
                  refine ⟨149771124448968689258599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 798779330394499676045861 149771124448968689258599)
                  ·
                    rfl

theorem cell21_656276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_656276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656276 prefixEnd_656276 := by exact prefixLift 656276
  have htrace : WordTrace (prefixWord ++ tailWord_656276) baseStart_656276 baseEnd_656276 := by
    simpa [prefixWord, tailWord_656276, baseEnd_656276] using wordTrace_append hprefix tailTrace_656276
  have hstable : (prefixWord ++ tailWord_656276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656276).length < 2 ^ (prefixWord ++ tailWord_656276).sum := by decide
  have hdescent : baseEnd_656276 < baseStart_656276 := by decide
  rcases family_descends (prefixWord ++ tailWord_656276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656290 : List Nat := [3, 3, 1, 2, 2, 1, 4, 5]
def baseStart_656290 : Nat := 118140960795 + 656290 * 2 ^ 59
def prefixEnd_656290 : Nat := 4983230072969 + 3 ^ 40 * 656290 * 2
def baseEnd_656290 : Nat := 49924773146569258675079

theorem tailTrace_656290 : CollatzResearch.WordTrace tailWord_656290 prefixEnd_656290 49924773146569258675079 := by
  unfold tailWord_656290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5984215698095222563383581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15957908528253926835689549 5984215698095222563383581)
  ·
    refine ⟨2244080886785708461268843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5984215698095222563383581 2244080886785708461268843)
    ·
      refine ⟨3366121330178562691903265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2244080886785708461268843 3366121330178562691903265)
      ·
        refine ⟨2524590997633922018927449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3366121330178562691903265 2524590997633922018927449)
        ·
          refine ⟨1893443248225441514195587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2524590997633922018927449 1893443248225441514195587)
          ·
            refine ⟨2840164872338162271293381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893443248225441514195587 2840164872338162271293381)
            ·
              refine ⟨532530913563405425867509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2840164872338162271293381 532530913563405425867509)
              ·
                refine ⟨49924773146569258675079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 532530913563405425867509 49924773146569258675079)
                ·
                  rfl

theorem cell21_656290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_656290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656290 prefixEnd_656290 := by exact prefixLift 656290
  have htrace : WordTrace (prefixWord ++ tailWord_656290) baseStart_656290 baseEnd_656290 := by
    simpa [prefixWord, tailWord_656290, baseEnd_656290] using wordTrace_append hprefix tailTrace_656290
  have hstable : (prefixWord ++ tailWord_656290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656290).length < 2 ^ (prefixWord ++ tailWord_656290).sum := by decide
  have hdescent : baseEnd_656290 < baseStart_656290 := by decide
  rcases family_descends (prefixWord ++ tailWord_656290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656318 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_656318 : Nat := 118140960795 + 656318 * 2 ^ 59
def prefixEnd_656318 : Nat := 4983230072969 + 3 ^ 40 * 656318 * 2
def baseEnd_656318 : Nat := 149780709421185949558513

theorem tailTrace_656318 : CollatzResearch.WordTrace tailWord_656318 prefixEnd_656318 149780709421185949558513 := by
  unfold tailWord_656318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2992235504534931379444201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15958589357519634023702405 2992235504534931379444201)
  ·
    refine ⟨2244176628401198534583151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2992235504534931379444201 2244176628401198534583151)
    ·
      refine ⟨3366264942601797801874727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2244176628401198534583151 3366264942601797801874727)
      ·
        refine ⟨5049397413902696702812091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3366264942601797801874727 5049397413902696702812091)
        ·
          refine ⟨7574096120854045054218137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5049397413902696702812091 7574096120854045054218137)
          ·
            refine ⟨5680572090640533790663603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7574096120854045054218137 5680572090640533790663603)
            ·
              refine ⟨8520858135960800685995405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5680572090640533790663603 8520858135960800685995405)
              ·
                refine ⟨3195321800985300257248277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8520858135960800685995405 3195321800985300257248277)
                ·
                  refine ⟨149780709421185949558513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3195321800985300257248277 149780709421185949558513)
                  ·
                    rfl

theorem cell21_656318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_656318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656318 prefixEnd_656318 := by exact prefixLift 656318
  have htrace : WordTrace (prefixWord ++ tailWord_656318) baseStart_656318 baseEnd_656318 := by
    simpa [prefixWord, tailWord_656318, baseEnd_656318] using wordTrace_append hprefix tailTrace_656318
  have hstable : (prefixWord ++ tailWord_656318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656318).length < 2 ^ (prefixWord ++ tailWord_656318).sum := by decide
  have hdescent : baseEnd_656318 < baseStart_656318 := by decide
  rcases family_descends (prefixWord ++ tailWord_656318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656335 : List Nat := [1, 1, 2, 1, 1, 6, 4, 1, 4]
def baseStart_656335 : Nat := 118140960795 + 656335 * 2 ^ 59
def prefixEnd_656335 : Nat := 4983230072969 + 3 ^ 40 * 656335 * 2
def baseEnd_656335 : Nat := 149784589052797697775145

theorem tailTrace_656335 : CollatzResearch.WordTrace tailWord_656335 prefixEnd_656335 149784589052797697775145 := by
  unfold tailWord_656335
  simp only [CollatzResearch.WordTrace]
  refine ⟨23938504077217862938922459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15959002718145241959281639 23938504077217862938922459)
  ·
    refine ⟨35907756115826794408383689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23938504077217862938922459 35907756115826794408383689)
    ·
      refine ⟨26930817086870095806287767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35907756115826794408383689 26930817086870095806287767)
      ·
        refine ⟨40396225630305143709431651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26930817086870095806287767 40396225630305143709431651)
        ·
          refine ⟨60594338445457715564147477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40396225630305143709431651 60594338445457715564147477)
          ·
            refine ⟨2840359614630830417069413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60594338445457715564147477 2840359614630830417069413)
            ·
              refine ⟨532567427743280703200515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2840359614630830417069413 532567427743280703200515)
              ·
                refine ⟨798851141614921054800773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532567427743280703200515 798851141614921054800773)
                ·
                  refine ⟨149784589052797697775145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 798851141614921054800773 149784589052797697775145)
                  ·
                    rfl

theorem cell21_656335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 4].length) (baseStart_656335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656335 prefixEnd_656335 := by exact prefixLift 656335
  have htrace : WordTrace (prefixWord ++ tailWord_656335) baseStart_656335 baseEnd_656335 := by
    simpa [prefixWord, tailWord_656335, baseEnd_656335] using wordTrace_append hprefix tailTrace_656335
  have hstable : (prefixWord ++ tailWord_656335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656335).length < 2 ^ (prefixWord ++ tailWord_656335).sum := by decide
  have hdescent : baseEnd_656335 < baseStart_656335 := by decide
  rcases family_descends (prefixWord ++ tailWord_656335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656349 : List Nat := [1, 4, 3, 1, 2, 1, 2, 7]
def baseStart_656349 : Nat := 118140960795 + 656349 * 2 ^ 59
def prefixEnd_656349 : Nat := 4983230072969 + 3 ^ 40 * 656349 * 2
def baseEnd_656349 : Nat := 49929261347845594847261

theorem tailTrace_656349 : CollatzResearch.WordTrace tailWord_656349 prefixEnd_656349 49929261347845594847261 := by
  unfold tailWord_656349
  simp only [CollatzResearch.WordTrace]
  refine ⟨23939014699167143329932101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15959343132778095553288067 23939014699167143329932101)
  ·
    refine ⟨4488565256093839374362269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23939014699167143329932101 4488565256093839374362269)
    ·
      refine ⟨1683211971035189765385851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4488565256093839374362269 1683211971035189765385851)
      ·
        refine ⟨2524817956552784648078777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683211971035189765385851 2524817956552784648078777)
        ·
          refine ⟨1893613467414588486059083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2524817956552784648078777 1893613467414588486059083)
          ·
            refine ⟨2840420201121882729088625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893613467414588486059083 2840420201121882729088625)
            ·
              refine ⟨2130315150841412046816469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2840420201121882729088625 2130315150841412046816469)
              ·
                refine ⟨49929261347845594847261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2130315150841412046816469 49929261347845594847261)
                ·
                  rfl

theorem cell21_656349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 7].length) (baseStart_656349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656349 prefixEnd_656349 := by exact prefixLift 656349
  have htrace : WordTrace (prefixWord ++ tailWord_656349) baseStart_656349 baseEnd_656349 := by
    simpa [prefixWord, tailWord_656349, baseEnd_656349] using wordTrace_append hprefix tailTrace_656349
  have hstable : (prefixWord ++ tailWord_656349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656349).length < 2 ^ (prefixWord ++ tailWord_656349).sum := by decide
  have hdescent : baseEnd_656349 < baseStart_656349 := by decide
  rcases family_descends (prefixWord ++ tailWord_656349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656490 : List Nat := [3, 1, 3, 2, 2, 2, 3, 2, 3]
def baseStart_656490 : Nat := 118140960795 + 656490 * 2 ^ 59
def prefixEnd_656490 : Nat := 4983230072969 + 3 ^ 40 * 656490 * 2
def baseEnd_656490 : Nat := 149819962164551872691495

theorem tailTrace_656490 : CollatzResearch.WordTrace tailWord_656490 prefixEnd_656490 149819962164551872691495 := by
  unfold tailWord_656490
  simp only [CollatzResearch.WordTrace]
  refine ⟨5986039347914081102703731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15962771594437549607209949 5986039347914081102703731)
  ·
    refine ⟨8979059021871121654055597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5986039347914081102703731 8979059021871121654055597)
    ·
      refine ⟨3367147133201670620270849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8979059021871121654055597 3367147133201670620270849)
      ·
        refine ⟨2525360349901252965203137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3367147133201670620270849 2525360349901252965203137)
        ·
          refine ⟨1894020262425939723902353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2525360349901252965203137 1894020262425939723902353)
          ·
            refine ⟨1420515196819454792926765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1894020262425939723902353 1420515196819454792926765)
            ·
              refine ⟨532693198807295547347537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1420515196819454792926765 532693198807295547347537)
              ·
                refine ⟨399519899105471660510653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532693198807295547347537 399519899105471660510653)
                ·
                  refine ⟨149819962164551872691495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399519899105471660510653 149819962164551872691495)
                  ·
                    rfl

theorem cell21_656490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_656490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656490 prefixEnd_656490 := by exact prefixLift 656490
  have htrace : WordTrace (prefixWord ++ tailWord_656490) baseStart_656490 baseEnd_656490 := by
    simpa [prefixWord, tailWord_656490, baseEnd_656490] using wordTrace_append hprefix tailTrace_656490
  have hstable : (prefixWord ++ tailWord_656490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656490).length < 2 ^ (prefixWord ++ tailWord_656490).sum := by decide
  have hdescent : baseEnd_656490 < baseStart_656490 := by decide
  rcases family_descends (prefixWord ++ tailWord_656490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656549 : List Nat := [1, 3, 1, 2, 1, 4, 4, 2, 3]
def baseStart_656549 : Nat := 118140960795 + 656549 * 2 ^ 59
def prefixEnd_656549 : Nat := 4983230072969 + 3 ^ 40 * 656549 * 2
def baseEnd_656549 : Nat := 149833426768380881208041

theorem tailTrace_656549 : CollatzResearch.WordTrace tailWord_656549 prefixEnd_656549 149833426768380881208041 := by
  unfold tailWord_656549
  simp only [CollatzResearch.WordTrace]
  refine ⟨23946309298442577487212701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15964206198961718324808467 23946309298442577487212701)
  ·
    refine ⟨8979865986915966557704763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23946309298442577487212701 8979865986915966557704763)
    ·
      refine ⟨13469798980373949836557145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8979865986915966557704763 13469798980373949836557145)
      ·
        refine ⟨10102349235280462377417859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13469798980373949836557145 10102349235280462377417859)
        ·
          refine ⟨15153523852920693566126789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10102349235280462377417859 15153523852920693566126789)
          ·
            refine ⟨2841285722422630043648773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15153523852920693566126789 2841285722422630043648773)
            ·
              refine ⟨532741072954243133184145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2841285722422630043648773 532741072954243133184145)
              ·
                refine ⟨399555804715682349888109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532741072954243133184145 399555804715682349888109)
                ·
                  refine ⟨149833426768380881208041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399555804715682349888109 149833426768380881208041)
                  ·
                    rfl

theorem cell21_656549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_656549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656549 prefixEnd_656549 := by exact prefixLift 656549
  have htrace : WordTrace (prefixWord ++ tailWord_656549) baseStart_656549 baseEnd_656549 := by
    simpa [prefixWord, tailWord_656549, baseEnd_656549] using wordTrace_append hprefix tailTrace_656549
  have hstable : (prefixWord ++ tailWord_656549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656549).length < 2 ^ (prefixWord ++ tailWord_656549).sum := by decide
  have hdescent : baseEnd_656549 < baseStart_656549 := by decide
  rcases family_descends (prefixWord ++ tailWord_656549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656566 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_656566 : Nat := 118140960795 + 656566 * 2 ^ 59
def prefixEnd_656566 : Nat := 4983230072969 + 3 ^ 40 * 656566 * 2
def baseEnd_656566 : Nat := 149837306399992629424673

theorem tailTrace_656566 : CollatzResearch.WordTrace tailWord_656566 prefixEnd_656566 149837306399992629424673 := by
  unfold tailWord_656566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1496683083711311836911347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15964619559587326260387701 1496683083711311836911347)
  ·
    refine ⟨2245024625566967755367021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1496683083711311836911347 2245024625566967755367021)
    ·
      refine ⟨841884234587612908262633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2245024625566967755367021 841884234587612908262633)
      ·
        refine ⟨631413175940709681196975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 841884234587612908262633 631413175940709681196975)
        ·
          refine ⟨947119763911064521795463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631413175940709681196975 947119763911064521795463)
          ·
            refine ⟨1420679645866596782693195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947119763911064521795463 1420679645866596782693195)
            ·
              refine ⟨2131019468799895174039793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420679645866596782693195 2131019468799895174039793)
              ·
                refine ⟨1598264601599921380529845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2131019468799895174039793 1598264601599921380529845)
                ·
                  refine ⟨149837306399992629424673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1598264601599921380529845 149837306399992629424673)
                  ·
                    rfl

theorem cell21_656566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_656566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656566 prefixEnd_656566 := by exact prefixLift 656566
  have htrace : WordTrace (prefixWord ++ tailWord_656566) baseStart_656566 baseEnd_656566 := by
    simpa [prefixWord, tailWord_656566, baseEnd_656566] using wordTrace_append hprefix tailTrace_656566
  have hstable : (prefixWord ++ tailWord_656566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656566).length < 2 ^ (prefixWord ++ tailWord_656566).sum := by decide
  have hdescent : baseEnd_656566 < baseStart_656566 := by decide
  rcases family_descends (prefixWord ++ tailWord_656566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656608 : List Nat := [2, 1, 1, 3, 1, 4, 2, 4, 3]
def baseStart_656608 : Nat := 118140960795 + 656608 * 2 ^ 59
def prefixEnd_656608 : Nat := 4983230072969 + 3 ^ 40 * 656608 * 2
def baseEnd_656608 : Nat := 149846891372209889724587

theorem tailTrace_656608 : CollatzResearch.WordTrace tailWord_656608 prefixEnd_656608 149846891372209889724587 := by
  unfold tailWord_656608
  simp only [CollatzResearch.WordTrace]
  refine ⟨11974230602614415281805239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15965640803485887042406985 11974230602614415281805239)
  ·
    refine ⟨17961345903921622922707859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11974230602614415281805239 17961345903921622922707859)
    ·
      refine ⟨26942018855882434384061789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17961345903921622922707859 26942018855882434384061789)
      ·
        refine ⟨10103257070955912894023171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26942018855882434384061789 10103257070955912894023171)
        ·
          refine ⟨15154885606433869341034757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10103257070955912894023171 15154885606433869341034757)
          ·
            refine ⟨2841541051206350501444017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15154885606433869341034757 2841541051206350501444017)
            ·
              refine ⟨2131155788404762876083013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841541051206350501444017 2131155788404762876083013)
              ·
                refine ⟨399591710325893039265565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2131155788404762876083013 399591710325893039265565)
                ·
                  refine ⟨149846891372209889724587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399591710325893039265565 149846891372209889724587)
                  ·
                    rfl

theorem cell21_656608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 3].length) (baseStart_656608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656608 prefixEnd_656608 := by exact prefixLift 656608
  have htrace : WordTrace (prefixWord ++ tailWord_656608) baseStart_656608 baseEnd_656608 := by
    simpa [prefixWord, tailWord_656608, baseEnd_656608] using wordTrace_append hprefix tailTrace_656608
  have hstable : (prefixWord ++ tailWord_656608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656608).length < 2 ^ (prefixWord ++ tailWord_656608).sum := by decide
  have hdescent : baseEnd_656608 < baseStart_656608 := by decide
  rcases family_descends (prefixWord ++ tailWord_656608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656622 : List Nat := [4, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_656622 : Nat := 118140960795 + 656622 * 2 ^ 59
def prefixEnd_656622 : Nat := 4983230072969 + 3 ^ 40 * 656622 * 2
def baseEnd_656622 : Nat := 149850086362948976491225

theorem tailTrace_656622 : CollatzResearch.WordTrace tailWord_656622 prefixEnd_656622 149850086362948976491225 := by
  unfold tailWord_656622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2993621478397263869327515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15965981218118740636413413 2993621478397263869327515)
  ·
    refine ⟨4490432217595895803991273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2993621478397263869327515 4490432217595895803991273)
    ·
      refine ⟨3367824163196921852993455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4490432217595895803991273 3367824163196921852993455)
      ·
        refine ⟨5051736244795382779490183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3367824163196921852993455 5051736244795382779490183)
        ·
          refine ⟨7577604367193074169235275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5051736244795382779490183 7577604367193074169235275)
          ·
            refine ⟨11366406550789611253852913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7577604367193074169235275 11366406550789611253852913)
            ·
              refine ⟨8524804913092208440389685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11366406550789611253852913 8524804913092208440389685)
              ·
                refine ⟨799200460602394541286533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8524804913092208440389685 799200460602394541286533)
                ·
                  refine ⟨149850086362948976491225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 799200460602394541286533 149850086362948976491225)
                  ·
                    rfl

theorem cell21_656622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_656622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656622 prefixEnd_656622 := by exact prefixLift 656622
  have htrace : WordTrace (prefixWord ++ tailWord_656622) baseStart_656622 baseEnd_656622 := by
    simpa [prefixWord, tailWord_656622, baseEnd_656622] using wordTrace_append hprefix tailTrace_656622
  have hstable : (prefixWord ++ tailWord_656622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656622).length < 2 ^ (prefixWord ++ tailWord_656622).sum := by decide
  have hdescent : baseEnd_656622 < baseStart_656622 := by decide
  rcases family_descends (prefixWord ++ tailWord_656622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656746 : List Nat := [3, 1, 3, 3, 2, 1, 3, 5]
def baseStart_656746 : Nat := 118140960795 + 656746 * 2 ^ 59
def prefixEnd_656746 : Nat := 4983230072969 + 3 ^ 40 * 656746 * 2
def baseEnd_656746 : Nat := 49959461617450772141435

theorem tailTrace_656746 : CollatzResearch.WordTrace tailWord_656746 prefixEnd_656746 49959461617450772141435 := by
  unfold tailWord_656746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5988373619682220033033523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15968996319152586754756061 5988373619682220033033523)
  ·
    refine ⟨8982560429523330049550285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5988373619682220033033523 8982560429523330049550285)
    ·
      refine ⟨3368460161071248768581357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8982560429523330049550285 3368460161071248768581357)
      ·
        refine ⟨1263172560401718288218009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3368460161071248768581357 1263172560401718288218009)
        ·
          refine ⟨947379420301288716163507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1263172560401718288218009 947379420301288716163507)
          ·
            refine ⟨1421069130451933074245261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947379420301288716163507 1421069130451933074245261)
            ·
              refine ⟨532900923919474902841973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1421069130451933074245261 532900923919474902841973)
              ·
                refine ⟨49959461617450772141435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 532900923919474902841973 49959461617450772141435)
                ·
                  rfl

theorem cell21_656746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_656746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656746 prefixEnd_656746 := by exact prefixLift 656746
  have htrace : WordTrace (prefixWord ++ tailWord_656746) baseStart_656746 baseEnd_656746 := by
    simpa [prefixWord, tailWord_656746, baseEnd_656746] using wordTrace_append hprefix tailTrace_656746
  have hstable : (prefixWord ++ tailWord_656746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656746).length < 2 ^ (prefixWord ++ tailWord_656746).sum := by decide
  have hdescent : baseEnd_656746 < baseStart_656746 := by decide
  rcases family_descends (prefixWord ++ tailWord_656746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656766 : List Nat := [4, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_656766 : Nat := 118140960795 + 656766 * 2 ^ 59
def prefixEnd_656766 : Nat := 4983230072969 + 3 ^ 40 * 656766 * 2
def baseEnd_656766 : Nat := 149882949124836726090931

theorem tailTrace_656766 : CollatzResearch.WordTrace tailWord_656766 prefixEnd_656766 149882949124836726090931 := by
  unfold tailWord_656766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2994277992332052943482769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15969482625770949031908101 2994277992332052943482769)
  ·
    refine ⟨2245708494249039707612077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2994277992332052943482769 2245708494249039707612077)
    ·
      refine ⟨842140685343389890354529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2245708494249039707612077 842140685343389890354529)
      ·
        refine ⟨631605514007542417765897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 842140685343389890354529 631605514007542417765897)
        ·
          refine ⟨473704135505656813324423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 631605514007542417765897 473704135505656813324423)
          ·
            refine ⟨710556203258485219986635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473704135505656813324423 710556203258485219986635)
            ·
              refine ⟨1065834304887727829979953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710556203258485219986635 1065834304887727829979953)
              ·
                refine ⟨799375728665795872484965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065834304887727829979953 799375728665795872484965)
                ·
                  refine ⟨149882949124836726090931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 799375728665795872484965 149882949124836726090931)
                  ·
                    rfl

theorem cell21_656766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_656766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656766 prefixEnd_656766 := by exact prefixLift 656766
  have htrace : WordTrace (prefixWord ++ tailWord_656766) baseStart_656766 baseEnd_656766 := by
    simpa [prefixWord, tailWord_656766, baseEnd_656766] using wordTrace_append hprefix tailTrace_656766
  have hstable : (prefixWord ++ tailWord_656766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656766).length < 2 ^ (prefixWord ++ tailWord_656766).sum := by decide
  have hdescent : baseEnd_656766 < baseStart_656766 := by decide
  rcases family_descends (prefixWord ++ tailWord_656766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656836 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 5]
def baseStart_656836 : Nat := 118140960795 + 656836 * 2 ^ 59
def prefixEnd_656836 : Nat := 4983230072969 + 3 ^ 40 * 656836 * 2
def baseEnd_656836 : Nat := 149898924078532159924121

theorem tailTrace_656836 : CollatzResearch.WordTrace tailWord_656836 prefixEnd_656836 149898924078532159924121 := by
  unfold tailWord_656836
  simp only [CollatzResearch.WordTrace]
  refine ⟨11978388524201412751455181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15971184698935217001940241 11978388524201412751455181)
  ·
    refine ⟨4491895696575529781795693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11978388524201412751455181 4491895696575529781795693)
    ·
      refine ⟨1684460886215823668173385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4491895696575529781795693 1684460886215823668173385)
      ·
        refine ⟨1263345664661867751130039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1684460886215823668173385 1263345664661867751130039)
        ·
          refine ⟨1895018496992801626695059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263345664661867751130039 1895018496992801626695059)
          ·
            refine ⟨2842527745489202440042589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895018496992801626695059 2842527745489202440042589)
            ·
              refine ⟨1065947904558450915015971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2842527745489202440042589 1065947904558450915015971)
              ·
                refine ⟨1598921856837676372523957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065947904558450915015971 1598921856837676372523957)
                ·
                  refine ⟨149898924078532159924121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1598921856837676372523957 149898924078532159924121)
                  ·
                    rfl

theorem cell21_656836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_656836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656836 prefixEnd_656836 := by exact prefixLift 656836
  have htrace : WordTrace (prefixWord ++ tailWord_656836) baseStart_656836 baseEnd_656836 := by
    simpa [prefixWord, tailWord_656836, baseEnd_656836] using wordTrace_append hprefix tailTrace_656836
  have hstable : (prefixWord ++ tailWord_656836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656836).length < 2 ^ (prefixWord ++ tailWord_656836).sum := by decide
  have hdescent : baseEnd_656836 < baseStart_656836 := by decide
  rcases family_descends (prefixWord ++ tailWord_656836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656847 : List Nat := [1, 1, 2, 1, 1, 4, 3, 8]
def baseStart_656847 : Nat := 118140960795 + 656847 * 2 ^ 59
def prefixEnd_656847 : Nat := 4983230072969 + 3 ^ 40 * 656847 * 2
def baseEnd_656847 : Nat := 49967144809466195080255

theorem tailTrace_656847 : CollatzResearch.WordTrace tailWord_656847 prefixEnd_656847 49967144809466195080255 := by
  unfold tailWord_656847
  simp only [CollatzResearch.WordTrace]
  refine ⟨23957178251362974381560795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15971452167575316254373863 23957178251362974381560795)
  ·
    refine ⟨35935767377044461572341193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23957178251362974381560795 35935767377044461572341193)
    ·
      refine ⟨26951825532783346179255895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35935767377044461572341193 26951825532783346179255895)
      ·
        refine ⟨40427738299175019268883843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26951825532783346179255895 40427738299175019268883843)
        ·
          refine ⟨60641607448762528903325765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40427738299175019268883843 60641607448762528903325765)
          ·
            refine ⟨11370301396642974169373581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60641607448762528903325765 11370301396642974169373581)
            ·
              refine ⟨4263863023741115313515093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11370301396642974169373581 4263863023741115313515093)
              ·
                refine ⟨49967144809466195080255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4263863023741115313515093 49967144809466195080255)
                ·
                  rfl

theorem cell21_656847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 8].length) (baseStart_656847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656847 prefixEnd_656847 := by exact prefixLift 656847
  have htrace : WordTrace (prefixWord ++ tailWord_656847) baseStart_656847 baseEnd_656847 := by
    simpa [prefixWord, tailWord_656847, baseEnd_656847] using wordTrace_append hprefix tailTrace_656847
  have hstable : (prefixWord ++ tailWord_656847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656847).length < 2 ^ (prefixWord ++ tailWord_656847).sum := by decide
  have hdescent : baseEnd_656847 < baseStart_656847 := by decide
  rcases family_descends (prefixWord ++ tailWord_656847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656898 : List Nat := [3, 4, 1, 2, 1, 3, 1, 6]
def baseStart_656898 : Nat := 118140960795 + 656898 * 2 ^ 59
def prefixEnd_656898 : Nat := 4983230072969 + 3 ^ 40 * 656898 * 2
def baseEnd_656898 : Nat := 49971024441077943296887

theorem tailTrace_656898 : CollatzResearch.WordTrace tailWord_656898 prefixEnd_656898 49971024441077943296887 := by
  unfold tailWord_656898
  simp only [CollatzResearch.WordTrace]
  refine ⟨5989759593544552522916837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15972692249452140061111565 5989759593544552522916837)
  ·
    refine ⟨1123079923789603598046907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5989759593544552522916837 1123079923789603598046907)
    ·
      refine ⟨1684619885684405397070361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1123079923789603598046907 1684619885684405397070361)
      ·
        refine ⟨1263464914263304047802771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1684619885684405397070361 1263464914263304047802771)
        ·
          refine ⟨1895197371394956071704157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263464914263304047802771 1895197371394956071704157)
          ·
            refine ⟨710699014273108526889059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1895197371394956071704157 710699014273108526889059)
            ·
              refine ⟨1066048521409662790333589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710699014273108526889059 1066048521409662790333589)
              ·
                refine ⟨49971024441077943296887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1066048521409662790333589 49971024441077943296887)
                ·
                  rfl

theorem cell21_656898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_656898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656898 prefixEnd_656898 := by exact prefixLift 656898
  have htrace : WordTrace (prefixWord ++ tailWord_656898) baseStart_656898 baseEnd_656898 := by
    simpa [prefixWord, tailWord_656898, baseEnd_656898] using wordTrace_append hprefix tailTrace_656898
  have hstable : (prefixWord ++ tailWord_656898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656898).length < 2 ^ (prefixWord ++ tailWord_656898).sum := by decide
  have hdescent : baseEnd_656898 < baseStart_656898 := by decide
  rcases family_descends (prefixWord ++ tailWord_656898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656999 : List Nat := [1, 1, 5, 1, 1, 1, 11]
def baseStart_656999 : Nat := 118140960795 + 656999 * 2 ^ 59
def prefixEnd_656999 : Nat := 4983230072969 + 3 ^ 40 * 656999 * 2
def baseEnd_656999 : Nat := 16659569211031122078569

theorem tailTrace_656999 : CollatzResearch.WordTrace tailWord_656999 prefixEnd_656999 16659569211031122078569 := by
  unfold tailWord_656999
  simp only [CollatzResearch.WordTrace]
  refine ⟨23962722146812304341094051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15975148097874869560729367 23962722146812304341094051)
  ·
    refine ⟨35944083220218456511641077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23962722146812304341094051 35944083220218456511641077)
    ·
      refine ⟨3369757801895480297966351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35944083220218456511641077 3369757801895480297966351)
      ·
        refine ⟨5054636702843220446949527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369757801895480297966351 5054636702843220446949527)
        ·
          refine ⟨7581955054264830670424291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5054636702843220446949527 7581955054264830670424291)
          ·
            refine ⟨11372932581397246005636437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7581955054264830670424291 11372932581397246005636437)
            ·
              refine ⟨16659569211031122078569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11372932581397246005636437 16659569211031122078569)
              ·
                rfl

theorem cell21_656999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 11].length) (baseStart_656999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_656999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_656999 prefixEnd_656999 := by exact prefixLift 656999
  have htrace : WordTrace (prefixWord ++ tailWord_656999) baseStart_656999 baseEnd_656999 := by
    simpa [prefixWord, tailWord_656999, baseEnd_656999] using wordTrace_append hprefix tailTrace_656999
  have hstable : (prefixWord ++ tailWord_656999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656999).length < 2 ^ (prefixWord ++ tailWord_656999).sum := by decide
  have hdescent : baseEnd_656999 < baseStart_656999 := by decide
  rcases family_descends (prefixWord ++ tailWord_656999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657005 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 5]
def baseStart_657005 : Nat := 118140960795 + 657005 * 2 ^ 59
def prefixEnd_657005 : Nat := 4983230072969 + 3 ^ 40 * 657005 * 2
def baseEnd_657005 : Nat := 149937492181025421607109

theorem tailTrace_657005 : CollatzResearch.WordTrace tailWord_657005 prefixEnd_657005 149937492181025421607109 := by
  unfold tailWord_657005
  simp only [CollatzResearch.WordTrace]
  refine ⟨23962940984790567365812469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15975293989860378243874979 23962940984790567365812469)
  ·
    refine ⟨2246525717324115690544919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23962940984790567365812469 2246525717324115690544919)
    ·
      refine ⟨3369788575986173535817379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2246525717324115690544919 3369788575986173535817379)
      ·
        refine ⟨5054682863979260303726069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369788575986173535817379 5054682863979260303726069)
        ·
          refine ⟨473876518498055653474319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5054682863979260303726069 473876518498055653474319)
          ·
            refine ⟨710814777747083480211479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473876518498055653474319 710814777747083480211479)
            ·
              refine ⟨1066222166620625220317219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710814777747083480211479 1066222166620625220317219)
              ·
                refine ⟨1599333249930937830475829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066222166620625220317219 1599333249930937830475829)
                ·
                  refine ⟨149937492181025421607109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1599333249930937830475829 149937492181025421607109)
                  ·
                    rfl

theorem cell21_657005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_657005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657005 prefixEnd_657005 := by exact prefixLift 657005
  have htrace : WordTrace (prefixWord ++ tailWord_657005) baseStart_657005 baseEnd_657005 := by
    simpa [prefixWord, tailWord_657005, baseEnd_657005] using wordTrace_append hprefix tailTrace_657005
  have hstable : (prefixWord ++ tailWord_657005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657005).length < 2 ^ (prefixWord ++ tailWord_657005).sum := by decide
  have hdescent : baseEnd_657005 < baseStart_657005 := by decide
  rcases family_descends (prefixWord ++ tailWord_657005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657061 : List Nat := [1, 3, 1, 2, 1, 2, 3, 4, 4]
def baseStart_657061 : Nat := 118140960795 + 657061 * 2 ^ 59
def prefixEnd_657061 : Nat := 4983230072969 + 3 ^ 40 * 657061 * 2
def baseEnd_657061 : Nat := 149950272143981768673661

theorem tailTrace_657061 : CollatzResearch.WordTrace tailWord_657061 prefixEnd_657061 149950272143981768673661 := by
  unfold tailWord_657061
  simp only [CollatzResearch.WordTrace]
  refine ⟨23964983472587688929851037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15976655648391792619900691 23964983472587688929851037)
  ·
    refine ⟨8986868802220383348694139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23964983472587688929851037 8986868802220383348694139)
    ·
      refine ⟨13480303203330575023041209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8986868802220383348694139 13480303203330575023041209)
      ·
        refine ⟨10110227402497931267280907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13480303203330575023041209 10110227402497931267280907)
        ·
          refine ⟨15165341103746896900921361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10110227402497931267280907 15165341103746896900921361)
          ·
            refine ⟨11374005827810172675691021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15165341103746896900921361 11374005827810172675691021)
            ·
              refine ⟨4265252185428814753384133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11374005827810172675691021 4265252185428814753384133)
              ·
                refine ⟨799734784767902766259525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4265252185428814753384133 799734784767902766259525)
                ·
                  refine ⟨149950272143981768673661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 799734784767902766259525 149950272143981768673661)
                  ·
                    rfl

theorem cell21_657061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_657061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657061 prefixEnd_657061 := by exact prefixLift 657061
  have htrace : WordTrace (prefixWord ++ tailWord_657061) baseStart_657061 baseEnd_657061 := by
    simpa [prefixWord, tailWord_657061, baseEnd_657061] using wordTrace_append hprefix tailTrace_657061
  have hstable : (prefixWord ++ tailWord_657061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657061).length < 2 ^ (prefixWord ++ tailWord_657061).sum := by decide
  have hdescent : baseEnd_657061 < baseStart_657061 := by decide
  rcases family_descends (prefixWord ++ tailWord_657061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657233 : List Nat := [1, 2, 2, 1, 5, 3, 2, 2, 3]
def baseStart_657233 : Nat := 118140960795 + 657233 * 2 ^ 59
def prefixEnd_657233 : Nat := 4983230072969 + 3 ^ 40 * 657233 * 2
def baseEnd_657233 : Nat := 149989524887347691806643

theorem tailTrace_657233 : CollatzResearch.WordTrace tailWord_657233 prefixEnd_657233 149989524887347691806643 := by
  unfold tailWord_657233
  simp only [CollatzResearch.WordTrace]
  refine ⟨23971256827964562305112353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15980837885309708203408235 23971256827964562305112353)
  ·
    refine ⟨17978442620973421728834265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23971256827964562305112353 17978442620973421728834265)
    ·
      refine ⟨13483831965730066296625699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17978442620973421728834265 13483831965730066296625699)
      ·
        refine ⟨20225747948595099444938549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13483831965730066296625699 20225747948595099444938549)
        ·
          refine ⟨1896163870180790572962989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20225747948595099444938549 1896163870180790572962989)
          ·
            refine ⟨711061451317796464861121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1896163870180790572962989 711061451317796464861121)
            ·
              refine ⟨533296088488347348645841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 711061451317796464861121 533296088488347348645841)
              ·
                refine ⟨399972066366260511484381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533296088488347348645841 399972066366260511484381)
                ·
                  refine ⟨149989524887347691806643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399972066366260511484381 149989524887347691806643)
                  ·
                    rfl

theorem cell21_657233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 3].length) (baseStart_657233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657233 prefixEnd_657233 := by exact prefixLift 657233
  have htrace : WordTrace (prefixWord ++ tailWord_657233) baseStart_657233 baseEnd_657233 := by
    simpa [prefixWord, tailWord_657233, baseEnd_657233] using wordTrace_append hprefix tailTrace_657233
  have hstable : (prefixWord ++ tailWord_657233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657233).length < 2 ^ (prefixWord ++ tailWord_657233).sum := by decide
  have hdescent : baseEnd_657233 < baseStart_657233 := by decide
  rcases family_descends (prefixWord ++ tailWord_657233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657379 : List Nat := [1, 1, 1, 6, 1, 2, 2, 7]
def baseStart_657379 : Nat := 118140960795 + 657379 * 2 ^ 59
def prefixEnd_657379 : Nat := 4983230072969 + 3 ^ 40 * 657379 * 2
def baseEnd_657379 : Nat := 50007614692161294124337

theorem tailTrace_657379 : CollatzResearch.WordTrace tailWord_657379 prefixEnd_657379 50007614692161294124337 := by
  unfold tailWord_657379
  simp only [CollatzResearch.WordTrace]
  refine ⟨23976581885435629239927191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15984387923623752826618127 23976581885435629239927191)
  ·
    refine ⟨35964872828153443859890787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23976581885435629239927191 35964872828153443859890787)
    ·
      refine ⟨53947309242230165789836181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35964872828153443859890787 53947309242230165789836181)
      ·
        refine ⟨2528780120729539021398571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53947309242230165789836181 2528780120729539021398571)
        ·
          refine ⟨3793170181094308532097857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2528780120729539021398571 3793170181094308532097857)
          ·
            refine ⟨2844877635820731399073393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3793170181094308532097857 2844877635820731399073393)
            ·
              refine ⟨2133658226865548549305045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2844877635820731399073393 2133658226865548549305045)
              ·
                refine ⟨50007614692161294124337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2133658226865548549305045 50007614692161294124337)
                ·
                  rfl

theorem cell21_657379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 7].length) (baseStart_657379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657379 prefixEnd_657379 := by exact prefixLift 657379
  have htrace : WordTrace (prefixWord ++ tailWord_657379) baseStart_657379 baseEnd_657379 := by
    simpa [prefixWord, tailWord_657379, baseEnd_657379] using wordTrace_append hprefix tailTrace_657379
  have hstable : (prefixWord ++ tailWord_657379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657379).length < 2 ^ (prefixWord ++ tailWord_657379).sum := by decide
  have hdescent : baseEnd_657379 < baseStart_657379 := by decide
  rcases family_descends (prefixWord ++ tailWord_657379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657458 : List Nat := [3, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_657458 : Nat := 118140960795 + 657458 * 2 ^ 59
def prefixEnd_657458 : Nat := 4983230072969 + 3 ^ 40 * 657458 * 2
def baseEnd_657458 : Nat := 150040872952797300556183

theorem tailTrace_657458 : CollatzResearch.WordTrace tailWord_657458 prefixEnd_657458 150040872952797300556183 := by
  unfold tailWord_657458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5994865813037356433013257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15986308834766283821368685 5994865813037356433013257)
  ·
    refine ⟨4496149359778017324759943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5994865813037356433013257 4496149359778017324759943)
    ·
      refine ⟨6744224039667025987139915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4496149359778017324759943 6744224039667025987139915)
      ·
        refine ⟨10116336059500538980709873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6744224039667025987139915 10116336059500538980709873)
        ·
          refine ⟨7587252044625404235532405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10116336059500538980709873 7587252044625404235532405)
          ·
            refine ⟨711304879183631647081163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7587252044625404235532405 711304879183631647081163)
            ·
              refine ⟨1066957318775447470621745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711304879183631647081163 1066957318775447470621745)
              ·
                refine ⟨800217989081585602966309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1066957318775447470621745 800217989081585602966309)
                ·
                  refine ⟨150040872952797300556183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 800217989081585602966309 150040872952797300556183)
                  ·
                    rfl

theorem cell21_657458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_657458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657458 prefixEnd_657458 := by exact prefixLift 657458
  have htrace : WordTrace (prefixWord ++ tailWord_657458) baseStart_657458 baseEnd_657458 := by
    simpa [prefixWord, tailWord_657458, baseEnd_657458] using wordTrace_append hprefix tailTrace_657458
  have hstable : (prefixWord ++ tailWord_657458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657458).length < 2 ^ (prefixWord ++ tailWord_657458).sum := by decide
  have hdescent : baseEnd_657458 < baseStart_657458 := by decide
  rcases family_descends (prefixWord ++ tailWord_657458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657486 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_657486 : Nat := 118140960795 + 657486 * 2 ^ 59
def prefixEnd_657486 : Nat := 4983230072969 + 3 ^ 40 * 657486 * 2
def baseEnd_657486 : Nat := 150047262934275474089459

theorem tailTrace_657486 : CollatzResearch.WordTrace tailWord_657486 prefixEnd_657486 150047262934275474089459 := by
  unfold tailWord_657486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2997560562005998314259039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15986989664031991009381541 2997560562005998314259039)
  ·
    refine ⟨4496340843008997471388559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2997560562005998314259039 4496340843008997471388559)
    ·
      refine ⟨6744511264513496207082839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4496340843008997471388559 6744511264513496207082839)
      ·
        refine ⟨10116766896770244310624259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6744511264513496207082839 10116766896770244310624259)
        ·
          refine ⟨15175150345155366465936389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10116766896770244310624259 15175150345155366465936389)
          ·
            refine ⟨2845340689716631212363073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15175150345155366465936389 2845340689716631212363073)
            ·
              refine ⟨2134005517287473409272305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2845340689716631212363073 2134005517287473409272305)
              ·
                refine ⟨1600504137965605056954229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2134005517287473409272305 1600504137965605056954229)
                ·
                  refine ⟨150047262934275474089459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1600504137965605056954229 150047262934275474089459)
                  ·
                    rfl

theorem cell21_657486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_657486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657486 prefixEnd_657486 := by exact prefixLift 657486
  have htrace : WordTrace (prefixWord ++ tailWord_657486) baseStart_657486 baseEnd_657486 := by
    simpa [prefixWord, tailWord_657486, baseEnd_657486] using wordTrace_append hprefix tailTrace_657486
  have hstable : (prefixWord ++ tailWord_657486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657486).length < 2 ^ (prefixWord ++ tailWord_657486).sum := by decide
  have hdescent : baseEnd_657486 < baseStart_657486 := by decide
  rcases family_descends (prefixWord ++ tailWord_657486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657517 : List Nat := [1, 5, 1, 1, 2, 1, 2, 4, 4]
def baseStart_657517 : Nat := 118140960795 + 657517 * 2 ^ 59
def prefixEnd_657517 : Nat := 4983230072969 + 3 ^ 40 * 657517 * 2
def baseEnd_657517 : Nat := 150054337556626309072729

theorem tailTrace_657517 : CollatzResearch.WordTrace tailWord_657517 prefixEnd_657517 150054337556626309072729 := by
  unfold tailWord_657517
  simp only [CollatzResearch.WordTrace]
  refine ⟨23981615158935678808450805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15987743439290452538967203 23981615158935678808450805)
  ·
    refine ⟨2248276421150219888292263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23981615158935678808450805 2248276421150219888292263)
    ·
      refine ⟨3372414631725329832438395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2248276421150219888292263 3372414631725329832438395)
      ·
        refine ⟨5058621947587994748657593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3372414631725329832438395 5058621947587994748657593)
        ·
          refine ⟨3793966460690996061493195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5058621947587994748657593 3793966460690996061493195)
          ·
            refine ⟨5690949691036494092239793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3793966460690996061493195 5690949691036494092239793)
            ·
              refine ⟨4268212268277370569179845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5690949691036494092239793 4268212268277370569179845)
              ·
                refine ⟨800289800302006981721221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4268212268277370569179845 800289800302006981721221)
                ·
                  refine ⟨150054337556626309072729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 800289800302006981721221 150054337556626309072729)
                  ·
                    rfl

theorem cell21_657517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_657517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657517 prefixEnd_657517 := by exact prefixLift 657517
  have htrace : WordTrace (prefixWord ++ tailWord_657517) baseStart_657517 baseEnd_657517 := by
    simpa [prefixWord, tailWord_657517, baseEnd_657517] using wordTrace_append hprefix tailTrace_657517
  have hstable : (prefixWord ++ tailWord_657517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657517).length < 2 ^ (prefixWord ++ tailWord_657517).sum := by decide
  have hdescent : baseEnd_657517 < baseStart_657517 := by decide
  rcases family_descends (prefixWord ++ tailWord_657517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657520 : List Nat := [2, 1, 1, 1, 5, 3, 3, 2, 3]
def baseStart_657520 : Nat := 118140960795 + 657520 * 2 ^ 59
def prefixEnd_657520 : Nat := 4983230072969 + 3 ^ 40 * 657520 * 2
def baseEnd_657520 : Nat := 150055022197498970522723

theorem tailTrace_657520 : CollatzResearch.WordTrace tailWord_657520 prefixEnd_657520 150055022197498970522723 := by
  unfold tailWord_657520
  simp only [CollatzResearch.WordTrace]
  refine ⟨11990862288962405160405007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15987816385283206880540009 11990862288962405160405007)
  ·
    refine ⟨17986293433443607740607511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11990862288962405160405007 17986293433443607740607511)
    ·
      refine ⟨26979440150165411610911267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17986293433443607740607511 26979440150165411610911267)
      ·
        refine ⟨40469160225248117416366901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26979440150165411610911267 40469160225248117416366901)
        ·
          refine ⟨3793983771117011007784397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40469160225248117416366901 3793983771117011007784397)
          ·
            refine ⟨1422743914168879127919149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3793983771117011007784397 1422743914168879127919149)
            ·
              refine ⟨533528967813329672969681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1422743914168879127919149 533528967813329672969681)
              ·
                refine ⟨400146725859997254727261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533528967813329672969681 400146725859997254727261)
                ·
                  refine ⟨150055022197498970522723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400146725859997254727261 150055022197498970522723)
                  ·
                    rfl

theorem cell21_657520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 3].length) (baseStart_657520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657520 prefixEnd_657520 := by exact prefixLift 657520
  have htrace : WordTrace (prefixWord ++ tailWord_657520) baseStart_657520 baseEnd_657520 := by
    simpa [prefixWord, tailWord_657520, baseEnd_657520] using wordTrace_append hprefix tailTrace_657520
  have hstable : (prefixWord ++ tailWord_657520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657520).length < 2 ^ (prefixWord ++ tailWord_657520).sum := by decide
  have hdescent : baseEnd_657520 < baseStart_657520 := by decide
  rcases family_descends (prefixWord ++ tailWord_657520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657545 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 7]
def baseStart_657545 : Nat := 118140960795 + 657545 * 2 ^ 59
def prefixEnd_657545 : Nat := 4983230072969 + 3 ^ 40 * 657545 * 2
def baseEnd_657545 : Nat := 150060727538104482606005

theorem tailTrace_657545 : CollatzResearch.WordTrace tailWord_657545 prefixEnd_657545 150060727538104482606005 := by
  unfold tailWord_657545
  simp only [CollatzResearch.WordTrace]
  refine ⟨23982636402834239590470089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15988424268556159726980059 23982636402834239590470089)
  ·
    refine ⟨17986977302125679692852567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23982636402834239590470089 17986977302125679692852567)
    ·
      refine ⟨26980465953188519539278851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17986977302125679692852567 26980465953188519539278851)
      ·
        refine ⟨40470698929782779308918277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26980465953188519539278851 40470698929782779308918277)
        ·
          refine ⟨7588256049334271120422177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40470698929782779308918277 7588256049334271120422177)
          ·
            refine ⟨5691192037000703340316633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7588256049334271120422177 5691192037000703340316633)
            ·
              refine ⟨4268394027750527505237475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5691192037000703340316633 4268394027750527505237475)
              ·
                refine ⟨6402591041625791257856213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268394027750527505237475 6402591041625791257856213)
                ·
                  refine ⟨150060727538104482606005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6402591041625791257856213 150060727538104482606005)
                  ·
                    rfl

theorem cell21_657545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_657545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657545 prefixEnd_657545 := by exact prefixLift 657545
  have htrace : WordTrace (prefixWord ++ tailWord_657545) baseStart_657545 baseEnd_657545 := by
    simpa [prefixWord, tailWord_657545, baseEnd_657545] using wordTrace_append hprefix tailTrace_657545
  have hstable : (prefixWord ++ tailWord_657545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657545).length < 2 ^ (prefixWord ++ tailWord_657545).sum := by decide
  have hdescent : baseEnd_657545 < baseStart_657545 := by decide
  rcases family_descends (prefixWord ++ tailWord_657545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657582 : List Nat := [4, 1, 4, 2, 1, 2, 1, 6]
def baseStart_657582 : Nat := 118140960795 + 657582 * 2 ^ 59
def prefixEnd_657582 : Nat := 4983230072969 + 3 ^ 40 * 657582 * 2
def baseEnd_657582 : Nat := 50023057147400213496421

theorem tailTrace_657582 : CollatzResearch.WordTrace tailWord_657582 prefixEnd_657582 50023057147400213496421 := by
  unfold tailWord_657582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2997998237962524363695875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15989323935800129939711333 2997998237962524363695875)
  ·
    refine ⟨4496997356943786545543813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2997998237962524363695875 4496997356943786545543813)
    ·
      refine ⟨843187004426959977289465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4496997356943786545543813 843187004426959977289465)
      ·
        refine ⟨632390253320219982967099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 843187004426959977289465 632390253320219982967099)
        ·
          refine ⟨948585379980329974450649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632390253320219982967099 948585379980329974450649)
          ·
            refine ⟨711439034985247480837987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 948585379980329974450649 711439034985247480837987)
            ·
              refine ⟨1067158552477871221256981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711439034985247480837987 1067158552477871221256981)
              ·
                refine ⟨50023057147400213496421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1067158552477871221256981 50023057147400213496421)
                ·
                  rfl

theorem cell21_657582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_657582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657582 prefixEnd_657582 := by exact prefixLift 657582
  have htrace : WordTrace (prefixWord ++ tailWord_657582) baseStart_657582 baseEnd_657582 := by
    simpa [prefixWord, tailWord_657582, baseEnd_657582] using wordTrace_append hprefix tailTrace_657582
  have hstable : (prefixWord ++ tailWord_657582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657582).length < 2 ^ (prefixWord ++ tailWord_657582).sum := by decide
  have hdescent : baseEnd_657582 < baseStart_657582 := by decide
  rcases family_descends (prefixWord ++ tailWord_657582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657672 : List Nat := [2, 1, 3, 2, 3, 3, 1, 3, 3]
def baseStart_657672 : Nat := 118140960795 + 657672 * 2 ^ 59
def prefixEnd_657672 : Nat := 4983230072969 + 3 ^ 40 * 657672 * 2
def baseEnd_657672 : Nat := 150089710668380483989079

theorem tailTrace_657672 : CollatzResearch.WordTrace tailWord_657672 prefixEnd_657672 150089710668380483989079 := by
  unfold tailWord_657672
  simp only [CollatzResearch.WordTrace]
  refine ⟨11993634236687070140171635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15991512315582760186895513 11993634236687070140171635)
  ·
    refine ⟨17990451355030605210257453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11993634236687070140171635 17990451355030605210257453)
    ·
      refine ⟨6746419258136476953846545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17990451355030605210257453 6746419258136476953846545)
      ·
        refine ⟨5059814443602357715384909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6746419258136476953846545 5059814443602357715384909)
        ·
          refine ⟨1897430416350884143269341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5059814443602357715384909 1897430416350884143269341)
          ·
            refine ⟨711536406131581553726003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1897430416350884143269341 711536406131581553726003)
            ·
              refine ⟨1067304609197372330589005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711536406131581553726003 1067304609197372330589005)
              ·
                refine ⟨400239228449014623970877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1067304609197372330589005 400239228449014623970877)
                ·
                  refine ⟨150089710668380483989079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400239228449014623970877 150089710668380483989079)
                  ·
                    rfl

theorem cell21_657672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 3].length) (baseStart_657672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657672 prefixEnd_657672 := by exact prefixLift 657672
  have htrace : WordTrace (prefixWord ++ tailWord_657672) baseStart_657672 baseEnd_657672 := by
    simpa [prefixWord, tailWord_657672, baseEnd_657672] using wordTrace_append hprefix tailTrace_657672
  have hstable : (prefixWord ++ tailWord_657672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657672).length < 2 ^ (prefixWord ++ tailWord_657672).sum := by decide
  have hdescent : baseEnd_657672 < baseStart_657672 := by decide
  rcases family_descends (prefixWord ++ tailWord_657672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657745 : List Nat := [1, 2, 2, 1, 4, 3, 2, 2, 4]
def baseStart_657745 : Nat := 118140960795 + 657745 * 2 ^ 59
def prefixEnd_657745 : Nat := 4983230072969 + 3 ^ 40 * 657745 * 2
def baseEnd_657745 : Nat := 150106370262948579272263

theorem tailTrace_657745 : CollatzResearch.WordTrace tailWord_657745 prefixEnd_657745 150106370262948579272263 := by
  unfold tailWord_657745
  simp only [CollatzResearch.WordTrace]
  refine ⟨23989931002109673747750689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15993287334739782498500459 23989931002109673747750689)
  ·
    refine ⟨17992448251582255310813017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23989931002109673747750689 17992448251582255310813017)
    ·
      refine ⟨13494336188686691483109763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17992448251582255310813017 13494336188686691483109763)
      ·
        refine ⟨20241504283030037224664645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13494336188686691483109763 20241504283030037224664645)
        ·
          refine ⟨3795282053068131979624621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20241504283030037224664645 3795282053068131979624621)
          ·
            refine ⟨1423230769900549492359233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3795282053068131979624621 1423230769900549492359233)
            ·
              refine ⟨1067423077425412119269425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1423230769900549492359233 1067423077425412119269425)
              ·
                refine ⟨800567308069059089452069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067423077425412119269425 800567308069059089452069)
                ·
                  refine ⟨150106370262948579272263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 800567308069059089452069 150106370262948579272263)
                  ·
                    rfl

theorem cell21_657745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_657745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657745 prefixEnd_657745 := by exact prefixLift 657745
  have htrace : WordTrace (prefixWord ++ tailWord_657745) baseStart_657745 baseEnd_657745 := by
    simpa [prefixWord, tailWord_657745, baseEnd_657745] using wordTrace_append hprefix tailTrace_657745
  have hstable : (prefixWord ++ tailWord_657745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657745).length < 2 ^ (prefixWord ++ tailWord_657745).sum := by decide
  have hdescent : baseEnd_657745 < baseStart_657745 := by decide
  rcases family_descends (prefixWord ++ tailWord_657745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657748 : List Nat := [2, 4, 1, 1, 2, 2, 4, 2, 3]
def baseStart_657748 : Nat := 118140960795 + 657748 * 2 ^ 59
def prefixEnd_657748 : Nat := 4983230072969 + 3 ^ 40 * 657748 * 2
def baseEnd_657748 : Nat := 150107054903821240722257

theorem tailTrace_657748 : CollatzResearch.WordTrace tailWord_657748 prefixEnd_657748 150107054903821240722257 := by
  unfold tailWord_657748
  simp only [CollatzResearch.WordTrace]
  refine ⟨11995020210549402630054949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15993360280732536840073265 11995020210549402630054949)
  ·
    refine ⟨2249066289478012993135303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11995020210549402630054949 2249066289478012993135303)
    ·
      refine ⟨3373599434217019489702955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2249066289478012993135303 3373599434217019489702955)
      ·
        refine ⟨5060399151325529234554433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3373599434217019489702955 5060399151325529234554433)
        ·
          refine ⟨3795299363494146925915825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5060399151325529234554433 3795299363494146925915825)
          ·
            refine ⟨2846474522620610194436869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3795299363494146925915825 2846474522620610194436869)
            ·
              refine ⟨533713972991364411456913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2846474522620610194436869 533713972991364411456913)
              ·
                refine ⟨400285479743523308592685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533713972991364411456913 400285479743523308592685)
                ·
                  refine ⟨150107054903821240722257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400285479743523308592685 150107054903821240722257)
                  ·
                    rfl

theorem cell21_657748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_657748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657748 prefixEnd_657748 := by exact prefixLift 657748
  have htrace : WordTrace (prefixWord ++ tailWord_657748) baseStart_657748 baseEnd_657748 := by
    simpa [prefixWord, tailWord_657748, baseEnd_657748] using wordTrace_append hprefix tailTrace_657748
  have hstable : (prefixWord ++ tailWord_657748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657748).length < 2 ^ (prefixWord ++ tailWord_657748).sum := by decide
  have hdescent : baseEnd_657748 < baseStart_657748 := by decide
  rcases family_descends (prefixWord ++ tailWord_657748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657804 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 6]
def baseStart_657804 : Nat := 118140960795 + 657804 * 2 ^ 59
def prefixEnd_657804 : Nat := 4983230072969 + 3 ^ 40 * 657804 * 2
def baseEnd_657804 : Nat := 150119834866777587788809

theorem tailTrace_657804 : CollatzResearch.WordTrace tailWord_657804 prefixEnd_657804 150119834866777587788809 := by
  unfold tailWord_657804
  simp only [CollatzResearch.WordTrace]
  refine ⟨11996041454447963412074233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15994721939263951216098977 11996041454447963412074233)
  ·
    refine ⟨8997031090835972559055675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11996041454447963412074233 8997031090835972559055675)
    ·
      refine ⟨13495546636253958838583513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8997031090835972559055675 13495546636253958838583513)
      ·
        refine ⟨10121659977190469128937635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13495546636253958838583513 10121659977190469128937635)
        ·
          refine ⟨15182489965785703693406453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10121659977190469128937635 15182489965785703693406453)
          ·
            refine ⟨1423358434292409721256855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15182489965785703693406453 1423358434292409721256855)
            ·
              refine ⟨2135037651438614581885283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423358434292409721256855 2135037651438614581885283)
              ·
                refine ⟨3202556477157921872827925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2135037651438614581885283 3202556477157921872827925)
                ·
                  refine ⟨150119834866777587788809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3202556477157921872827925 150119834866777587788809)
                  ·
                    rfl

theorem cell21_657804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_657804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657804 prefixEnd_657804 := by exact prefixLift 657804
  have htrace : WordTrace (prefixWord ++ tailWord_657804) baseStart_657804 baseEnd_657804 := by
    simpa [prefixWord, tailWord_657804, baseEnd_657804] using wordTrace_append hprefix tailTrace_657804
  have hstable : (prefixWord ++ tailWord_657804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657804).length < 2 ^ (prefixWord ++ tailWord_657804).sum := by decide
  have hdescent : baseEnd_657804 < baseStart_657804 := by decide
  rcases family_descends (prefixWord ++ tailWord_657804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657965 : List Nat := [1, 5, 4, 1, 2, 1, 1, 2, 4]
def baseStart_657965 : Nat := 118140960795 + 657965 * 2 ^ 59
def prefixEnd_657965 : Nat := 4983230072969 + 3 ^ 40 * 657965 * 2
def baseEnd_657965 : Nat := 150156577260277085605147

theorem tailTrace_657965 : CollatzResearch.WordTrace tailWord_657965 prefixEnd_657965 150156577260277085605147 := by
  unfold tailWord_657965
  simp only [CollatzResearch.WordTrace]
  refine ⟨23997955061312651320759349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15998636707541767547172899 23997955061312651320759349)
  ·
    refine ⟨2249808286998061061321189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23997955061312651320759349 2249808286998061061321189)
    ·
      refine ⟨421839053812136448997723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2249808286998061061321189 421839053812136448997723)
      ·
        refine ⟨632758580718204673496585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421839053812136448997723 632758580718204673496585)
        ·
          refine ⟨474568935538653505122439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 632758580718204673496585 474568935538653505122439)
          ·
            refine ⟨711853403307980257683659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474568935538653505122439 711853403307980257683659)
            ·
              refine ⟨1067780104961970386525489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711853403307980257683659 1067780104961970386525489)
              ·
                refine ⟨800835078721477789894117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067780104961970386525489 800835078721477789894117)
                ·
                  refine ⟨150156577260277085605147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 800835078721477789894117 150156577260277085605147)
                  ·
                    rfl

theorem cell21_657965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_657965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_657965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_657965 prefixEnd_657965 := by exact prefixLift 657965
  have htrace : WordTrace (prefixWord ++ tailWord_657965) baseStart_657965 baseEnd_657965 := by
    simpa [prefixWord, tailWord_657965, baseEnd_657965] using wordTrace_append hprefix tailTrace_657965
  have hstable : (prefixWord ++ tailWord_657965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657965).length < 2 ^ (prefixWord ++ tailWord_657965).sum := by decide
  have hdescent : baseEnd_657965 < baseStart_657965 := by decide
  rcases family_descends (prefixWord ++ tailWord_657965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658001 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 5]
def baseStart_658001 : Nat := 118140960795 + 658001 * 2 ^ 59
def prefixEnd_658001 : Nat := 4983230072969 + 3 ^ 40 * 658001 * 2
def baseEnd_658001 : Nat := 150164792950749023005073

theorem tailTrace_658001 : CollatzResearch.WordTrace tailWord_658001 prefixEnd_658001 150164792950749023005073 := by
  unfold tailWord_658001
  simp only [CollatzResearch.WordTrace]
  refine ⟨23999268089182229469069857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15999512059454819646046571 23999268089182229469069857)
  ·
    refine ⟨17999451066886672101802393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23999268089182229469069857 17999451066886672101802393)
    ·
      refine ⟨13499588300165004076351795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17999451066886672101802393 13499588300165004076351795)
      ·
        refine ⟨20249382450247506114527693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13499588300165004076351795 20249382450247506114527693)
        ·
          refine ⟨7593518418842814792947885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20249382450247506114527693 7593518418842814792947885)
          ·
            refine ⟨2847569407066055547355457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7593518418842814792947885 2847569407066055547355457)
            ·
              refine ⟨2135677055299541660516593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2847569407066055547355457 2135677055299541660516593)
              ·
                refine ⟨1601757791474656245387445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2135677055299541660516593 1601757791474656245387445)
                ·
                  refine ⟨150164792950749023005073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1601757791474656245387445 150164792950749023005073)
                  ·
                    rfl

theorem cell21_658001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_658001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658001 prefixEnd_658001 := by exact prefixLift 658001
  have htrace : WordTrace (prefixWord ++ tailWord_658001) baseStart_658001 baseEnd_658001 := by
    simpa [prefixWord, tailWord_658001, baseEnd_658001] using wordTrace_append hprefix tailTrace_658001
  have hstable : (prefixWord ++ tailWord_658001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658001).length < 2 ^ (prefixWord ++ tailWord_658001).sum := by decide
  have hdescent : baseEnd_658001 < baseStart_658001 := by decide
  rcases family_descends (prefixWord ++ tailWord_658001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658004 : List Nat := [2, 4, 1, 1, 1, 5, 2, 5]
def baseStart_658004 : Nat := 118140960795 + 658004 * 2 ^ 59
def prefixEnd_658004 : Nat := 4983230072969 + 3 ^ 40 * 658004 * 2
def baseEnd_658004 : Nat := 50055159197207228151689

theorem tailTrace_658004 : CollatzResearch.WordTrace tailWord_658004 prefixEnd_658004 50055159197207228151689 := by
  unfold tailWord_658004
  simp only [CollatzResearch.WordTrace]
  refine ⟨11999688754085680490714533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15999585005447573987619377 11999688754085680490714533)
  ·
    refine ⟨2249941641391065092008975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11999688754085680490714533 2249941641391065092008975)
    ·
      refine ⟨3374912462086597638013463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2249941641391065092008975 3374912462086597638013463)
      ·
        refine ⟨5062368693129896457020195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3374912462086597638013463 5062368693129896457020195)
        ·
          refine ⟨7593553039694844685530293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5062368693129896457020195 7593553039694844685530293)
          ·
            refine ⟨711895597471391689268465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7593553039694844685530293 711895597471391689268465)
            ·
              refine ⟨533921698103543766951349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 711895597471391689268465 533921698103543766951349)
              ·
                refine ⟨50055159197207228151689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 533921698103543766951349 50055159197207228151689)
                ·
                  rfl

theorem cell21_658004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 5].length) (baseStart_658004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658004 prefixEnd_658004 := by exact prefixLift 658004
  have htrace : WordTrace (prefixWord ++ tailWord_658004) baseStart_658004 baseEnd_658004 := by
    simpa [prefixWord, tailWord_658004, baseEnd_658004] using wordTrace_append hprefix tailTrace_658004
  have hstable : (prefixWord ++ tailWord_658004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658004).length < 2 ^ (prefixWord ++ tailWord_658004).sum := by decide
  have hdescent : baseEnd_658004 < baseStart_658004 := by decide
  rcases family_descends (prefixWord ++ tailWord_658004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658097 : List Nat := [1, 2, 2, 6, 2, 1, 1, 6]
def baseStart_658097 : Nat := 118140960795 + 658097 * 2 ^ 59
def prefixEnd_658097 : Nat := 4983230072969 + 3 ^ 40 * 658097 * 2
def baseEnd_658097 : Nat := 50062233819558063134959

theorem tailTrace_658097 : CollatzResearch.WordTrace tailWord_658097 prefixEnd_658097 50062233819558063134959 := by
  unfold tailWord_658097
  simp only [CollatzResearch.WordTrace]
  refine ⟨24002769496834437864564545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16001846331222958576376363 24002769496834437864564545)
  ·
    refine ⟨18002077122625828398423409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24002769496834437864564545 18002077122625828398423409)
    ·
      refine ⟨13501557841969371298817557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18002077122625828398423409 13501557841969371298817557)
      ·
        refine ⟨632885523842314279632073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13501557841969371298817557 632885523842314279632073)
        ·
          refine ⟨474664142881735709724055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 632885523842314279632073 474664142881735709724055)
          ·
            refine ⟨711996214322603564586083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474664142881735709724055 711996214322603564586083)
            ·
              refine ⟨1067994321483905346879125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711996214322603564586083 1067994321483905346879125)
              ·
                refine ⟨50062233819558063134959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1067994321483905346879125 50062233819558063134959)
                ·
                  rfl

theorem cell21_658097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 6].length) (baseStart_658097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658097 prefixEnd_658097 := by exact prefixLift 658097
  have htrace : WordTrace (prefixWord ++ tailWord_658097) baseStart_658097 baseEnd_658097 := by
    simpa [prefixWord, tailWord_658097, baseEnd_658097] using wordTrace_append hprefix tailTrace_658097
  have hstable : (prefixWord ++ tailWord_658097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658097).length < 2 ^ (prefixWord ++ tailWord_658097).sum := by decide
  have hdescent : baseEnd_658097 < baseStart_658097 := by decide
  rcases family_descends (prefixWord ++ tailWord_658097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658108 : List Nat := [2, 2, 2, 3, 1, 1, 1, 5, 4]
def baseStart_658108 : Nat := 118140960795 + 658108 * 2 ^ 59
def prefixEnd_658108 : Nat := 4983230072969 + 3 ^ 40 * 658108 * 2
def baseEnd_658108 : Nat := 150189211808540614721521

theorem tailTrace_658108 : CollatzResearch.WordTrace tailWord_658108 prefixEnd_658108 150189211808540614721521 := by
  unfold tailWord_658108
  simp only [CollatzResearch.WordTrace]
  refine ⟨12001585349897293371607489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16002113799863057828809985 12001585349897293371607489)
  ·
    refine ⟨9001189012422970028705617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12001585349897293371607489 9001189012422970028705617)
    ·
      refine ⟨6750891759317227521529213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9001189012422970028705617 6750891759317227521529213)
      ·
        refine ⟨2531584409743960320573455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6750891759317227521529213 2531584409743960320573455)
        ·
          refine ⟨3797376614615940480860183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2531584409743960320573455 3797376614615940480860183)
          ·
            refine ⟨5696064921923910721290275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3797376614615940480860183 5696064921923910721290275)
            ·
              refine ⟨8544097382885866081935413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5696064921923910721290275 8544097382885866081935413)
              ·
                refine ⟨801009129645549945181445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8544097382885866081935413 801009129645549945181445)
                ·
                  refine ⟨150189211808540614721521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801009129645549945181445 150189211808540614721521)
                  ·
                    rfl

theorem cell21_658108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_658108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658108 prefixEnd_658108 := by exact prefixLift 658108
  have htrace : WordTrace (prefixWord ++ tailWord_658108) baseStart_658108 baseEnd_658108 := by
    simpa [prefixWord, tailWord_658108, baseEnd_658108] using wordTrace_append hprefix tailTrace_658108
  have hstable : (prefixWord ++ tailWord_658108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658108).length < 2 ^ (prefixWord ++ tailWord_658108).sum := by decide
  have hdescent : baseEnd_658108 < baseStart_658108 := by decide
  rcases family_descends (prefixWord ++ tailWord_658108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658218 : List Nat := [3, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_658218 : Nat := 118140960795 + 658218 * 2 ^ 59
def prefixEnd_658218 : Nat := 4983230072969 + 3 ^ 40 * 658218 * 2
def baseEnd_658218 : Nat := 150214315307204867887963

theorem tailTrace_658218 : CollatzResearch.WordTrace tailWord_658218 prefixEnd_658218 150214315307204867887963 := by
  unfold tailWord_658218
  simp only [CollatzResearch.WordTrace]
  refine ⟨6001795682349018882429827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16004788486264050353146205 6001795682349018882429827)
  ·
    refine ⟨9002693523523528323644741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6001795682349018882429827 9002693523523528323644741)
    ·
      refine ⟨1688005035660661560683389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9002693523523528323644741 1688005035660661560683389)
      ·
        refine ⟨633001888372748085256271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1688005035660661560683389 633001888372748085256271)
        ·
          refine ⟨949502832559122127884407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633001888372748085256271 949502832559122127884407)
          ·
            refine ⟨1424254248838683191826611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949502832559122127884407 1424254248838683191826611)
            ·
              refine ⟨2136381373258024787739917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424254248838683191826611 2136381373258024787739917)
              ·
                refine ⟨801143014971759295402469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2136381373258024787739917 801143014971759295402469)
                ·
                  refine ⟨150214315307204867887963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801143014971759295402469 150214315307204867887963)
                  ·
                    rfl

theorem cell21_658218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_658218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658218 prefixEnd_658218 := by exact prefixLift 658218
  have htrace : WordTrace (prefixWord ++ tailWord_658218) baseStart_658218 baseEnd_658218 := by
    simpa [prefixWord, tailWord_658218, baseEnd_658218] using wordTrace_append hprefix tailTrace_658218
  have hstable : (prefixWord ++ tailWord_658218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658218).length < 2 ^ (prefixWord ++ tailWord_658218).sum := by decide
  have hdescent : baseEnd_658218 < baseStart_658218 := by decide
  rcases family_descends (prefixWord ++ tailWord_658218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658257 : List Nat := [1, 2, 2, 1, 15]
def baseStart_658257 : Nat := 118140960795 + 658257 * 2 ^ 59
def prefixEnd_658257 : Nat := 4983230072969 + 3 ^ 40 * 658257 * 2
def baseEnd_658257 : Nat := 1854607600475919342443

theorem tailTrace_658257 : CollatzResearch.WordTrace tailWord_658257 prefixEnd_658257 1854607600475919342443 := by
  unfold tailWord_658257
  simp only [CollatzResearch.WordTrace]
  refine ⟨24008605176254785190389025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16005736784169856793592683 24008605176254785190389025)
  ·
    refine ⟨18006453882191088892791769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24008605176254785190389025 18006453882191088892791769)
    ·
      refine ⟨13504840411643316669593827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18006453882191088892791769 13504840411643316669593827)
      ·
        refine ⟨20257260617464975004390741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13504840411643316669593827 20257260617464975004390741)
        ·
          refine ⟨1854607600475919342443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 20257260617464975004390741 1854607600475919342443)
          ·
            rfl

theorem cell21_658257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 15].length) (baseStart_658257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658257 prefixEnd_658257 := by exact prefixLift 658257
  have htrace : WordTrace (prefixWord ++ tailWord_658257) baseStart_658257 baseEnd_658257 := by
    simpa [prefixWord, tailWord_658257, baseEnd_658257] using wordTrace_append hprefix tailTrace_658257
  have hstable : (prefixWord ++ tailWord_658257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658257).length < 2 ^ (prefixWord ++ tailWord_658257).sum := by decide
  have hdescent : baseEnd_658257 < baseStart_658257 := by decide
  rcases family_descends (prefixWord ++ tailWord_658257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658263 : List Nat := [1, 1, 3, 2, 4, 1, 4, 2, 3]
def baseStart_658263 : Nat := 118140960795 + 658263 * 2 ^ 59
def prefixEnd_658263 : Nat := 4983230072969 + 3 ^ 40 * 658263 * 2
def baseEnd_658263 : Nat := 150224584920294789637871

theorem tailTrace_658263 : CollatzResearch.WordTrace tailWord_658263 prefixEnd_658263 150224584920294789637871 := by
  unfold tailWord_658263
  simp only [CollatzResearch.WordTrace]
  refine ⟨24008824014233048215107443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16005882676155365476738295 24008824014233048215107443)
  ·
    refine ⟨36013236021349572322661165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24008824014233048215107443 36013236021349572322661165)
    ·
      refine ⟨13504963508006089620997937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36013236021349572322661165 13504963508006089620997937)
      ·
        refine ⟨10128722631004567215748453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13504963508006089620997937 10128722631004567215748453)
        ·
          refine ⟨1899135493313356352952835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10128722631004567215748453 1899135493313356352952835)
          ·
            refine ⟨2848703239970034529429253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899135493313356352952835 2848703239970034529429253)
            ·
              refine ⟨534131857494381474267985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2848703239970034529429253 534131857494381474267985)
              ·
                refine ⟨400598893120786105700989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534131857494381474267985 400598893120786105700989)
                ·
                  refine ⟨150224584920294789637871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400598893120786105700989 150224584920294789637871)
                  ·
                    rfl

theorem cell21_658263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 3].length) (baseStart_658263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658263 prefixEnd_658263 := by exact prefixLift 658263
  have htrace : WordTrace (prefixWord ++ tailWord_658263) baseStart_658263 baseEnd_658263 := by
    simpa [prefixWord, tailWord_658263, baseEnd_658263] using wordTrace_append hprefix tailTrace_658263
  have hstable : (prefixWord ++ tailWord_658263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658263).length < 2 ^ (prefixWord ++ tailWord_658263).sum := by decide
  have hdescent : baseEnd_658263 < baseStart_658263 := by decide
  rcases family_descends (prefixWord ++ tailWord_658263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658288 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 7]
def baseStart_658288 : Nat := 118140960795 + 658288 * 2 ^ 59
def prefixEnd_658288 : Nat := 4983230072969 + 3 ^ 40 * 658288 * 2
def baseEnd_658288 : Nat := 150230290260900301721153

theorem tailTrace_658288 : CollatzResearch.WordTrace tailWord_658288 prefixEnd_658288 150230290260900301721153 := by
  unfold tailWord_658288
  simp only [CollatzResearch.WordTrace]
  refine ⟨12004867919571238742383759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16006490559428318323178345 12004867919571238742383759)
  ·
    refine ⟨18007301879356858113575639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12004867919571238742383759 18007301879356858113575639)
    ·
      refine ⟨27010952819035287170363459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18007301879356858113575639 27010952819035287170363459)
      ·
        refine ⟨40516429228552930755545189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27010952819035287170363459 40516429228552930755545189)
        ·
          refine ⟨7596830480353674516664723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40516429228552930755545189 7596830480353674516664723)
          ·
            refine ⟨11395245720530511774997085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7596830480353674516664723 11395245720530511774997085)
            ·
              refine ⟨4273217145198941915623907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11395245720530511774997085 4273217145198941915623907)
              ·
                refine ⟨6409825717798412873435861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4273217145198941915623907 6409825717798412873435861)
                ·
                  refine ⟨150230290260900301721153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6409825717798412873435861 150230290260900301721153)
                  ·
                    rfl

theorem cell21_658288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_658288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658288 prefixEnd_658288 := by exact prefixLift 658288
  have htrace : WordTrace (prefixWord ++ tailWord_658288) baseStart_658288 baseEnd_658288 := by
    simpa [prefixWord, tailWord_658288, baseEnd_658288] using wordTrace_append hprefix tailTrace_658288
  have hstable : (prefixWord ++ tailWord_658288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658288).length < 2 ^ (prefixWord ++ tailWord_658288).sum := by decide
  have hdescent : baseEnd_658288 < baseStart_658288 := by decide
  rcases family_descends (prefixWord ++ tailWord_658288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658356 : List Nat := [2, 5, 2, 1, 1, 1, 3, 3, 3]
def baseStart_658356 : Nat := 118140960795 + 658356 * 2 ^ 59
def prefixEnd_658356 : Nat := 4983230072969 + 3 ^ 40 * 658356 * 2
def baseEnd_658356 : Nat := 150245808787347294587681

theorem tailTrace_658356 : CollatzResearch.WordTrace tailWord_658356 prefixEnd_658356 150245808787347294587681 := by
  unfold tailWord_658356
  simp only [CollatzResearch.WordTrace]
  refine ⟨12006108001448062549121461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16008144001930750065495281 12006108001448062549121461)
  ·
    refine ⟨1125572625135755863980137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12006108001448062549121461 1125572625135755863980137)
    ·
      refine ⟨844179468851816897985103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1125572625135755863980137 844179468851816897985103)
      ·
        refine ⟨1266269203277725346977655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844179468851816897985103 1266269203277725346977655)
        ·
          refine ⟨1899403804916588020466483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266269203277725346977655 1899403804916588020466483)
          ·
            refine ⟨2849105707374882030699725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899403804916588020466483 2849105707374882030699725)
            ·
              refine ⟨1068414640265580761512397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2849105707374882030699725 1068414640265580761512397)
              ·
                refine ⟨400655490099592785567149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1068414640265580761512397 400655490099592785567149)
                ·
                  refine ⟨150245808787347294587681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400655490099592785567149 150245808787347294587681)
                  ·
                    rfl

theorem cell21_658356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_658356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658356 prefixEnd_658356 := by exact prefixLift 658356
  have htrace : WordTrace (prefixWord ++ tailWord_658356) baseStart_658356 baseEnd_658356 := by
    simpa [prefixWord, tailWord_658356, baseEnd_658356] using wordTrace_append hprefix tailTrace_658356
  have hstable : (prefixWord ++ tailWord_658356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658356).length < 2 ^ (prefixWord ++ tailWord_658356).sum := by decide
  have hdescent : baseEnd_658356 < baseStart_658356 := by decide
  rcases family_descends (prefixWord ++ tailWord_658356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658488 : List Nat := [2, 1, 2, 1, 5, 1, 3, 2, 4]
def baseStart_658488 : Nat := 118140960795 + 658488 * 2 ^ 59
def prefixEnd_658488 : Nat := 4983230072969 + 3 ^ 40 * 658488 * 2
def baseEnd_658488 : Nat := 150275932985744398387411

theorem tailTrace_658488 : CollatzResearch.WordTrace tailWord_658488 prefixEnd_658488 150275932985744398387411 := by
  unfold tailWord_658488
  simp only [CollatzResearch.WordTrace]
  refine ⟨12008515219208955821024059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16011353625611941094698745 12008515219208955821024059)
  ·
    refine ⟨18012772828813433731536089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12008515219208955821024059 18012772828813433731536089)
    ·
      refine ⟨13509579621610075298652067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18012772828813433731536089 13509579621610075298652067)
      ·
        refine ⟨20264369432415112947978101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13509579621610075298652067 20264369432415112947978101)
        ·
          refine ⟨1899784634288916838872947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20264369432415112947978101 1899784634288916838872947)
          ·
            refine ⟨2849676951433375258309421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899784634288916838872947 2849676951433375258309421)
            ·
              refine ⟨1068628856787515721866033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2849676951433375258309421 1068628856787515721866033)
              ·
                refine ⟨801471642590636791399525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1068628856787515721866033 801471642590636791399525)
                ·
                  refine ⟨150275932985744398387411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801471642590636791399525 150275932985744398387411)
                  ·
                    rfl

theorem cell21_658488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_658488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658488 prefixEnd_658488 := by exact prefixLift 658488
  have htrace : WordTrace (prefixWord ++ tailWord_658488) baseStart_658488 baseEnd_658488 := by
    simpa [prefixWord, tailWord_658488, baseEnd_658488] using wordTrace_append hprefix tailTrace_658488
  have hstable : (prefixWord ++ tailWord_658488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658488).length < 2 ^ (prefixWord ++ tailWord_658488).sum := by decide
  have hdescent : baseEnd_658488 < baseStart_658488 := by decide
  rcases family_descends (prefixWord ++ tailWord_658488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658525 : List Nat := [1, 4, 4, 1, 3, 1, 1, 3, 3]
def baseStart_658525 : Nat := 118140960795 + 658525 * 2 ^ 59
def prefixEnd_658525 : Nat := 4983230072969 + 3 ^ 40 * 658525 * 2
def baseEnd_658525 : Nat := 150284376889840556270669

theorem tailTrace_658525 : CollatzResearch.WordTrace tailWord_658525 prefixEnd_658525 150284376889840556270669 := by
  unfold tailWord_658525
  simp only [CollatzResearch.WordTrace]
  refine ⟨24018379939283866961145029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16012253292855911307430019 24018379939283866961145029)
  ·
    refine ⟨4503446238615725055214693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24018379939283866961145029 4503446238615725055214693)
    ·
      refine ⟨844396169740448447852755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4503446238615725055214693 844396169740448447852755)
      ·
        refine ⟨1266594254610672671779133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844396169740448447852755 1266594254610672671779133)
        ·
          refine ⟨474972845479002251917175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1266594254610672671779133 474972845479002251917175)
          ·
            refine ⟨712459268218503377875763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474972845479002251917175 712459268218503377875763)
            ·
              refine ⟨1068688902327755066813645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712459268218503377875763 1068688902327755066813645)
              ·
                refine ⟨400758338372908150055117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1068688902327755066813645 400758338372908150055117)
                ·
                  refine ⟨150284376889840556270669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400758338372908150055117 150284376889840556270669)
                  ·
                    rfl

theorem cell21_658525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_658525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658525 prefixEnd_658525 := by exact prefixLift 658525
  have htrace : WordTrace (prefixWord ++ tailWord_658525) baseStart_658525 baseEnd_658525 := by
    simpa [prefixWord, tailWord_658525, baseEnd_658525] using wordTrace_append hprefix tailTrace_658525
  have hstable : (prefixWord ++ tailWord_658525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658525).length < 2 ^ (prefixWord ++ tailWord_658525).sum := by decide
  have hdescent : baseEnd_658525 < baseStart_658525 := by decide
  rcases family_descends (prefixWord ++ tailWord_658525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658536 : List Nat := [2, 1, 4, 4, 2, 1, 7]
def baseStart_658536 : Nat := 118140960795 + 658536 * 2 ^ 59
def prefixEnd_658536 : Nat := 4983230072969 + 3 ^ 40 * 658536 * 2
def baseEnd_658536 : Nat := 16698543026634109065257

theorem tailTrace_658536 : CollatzResearch.WordTrace tailWord_658536 prefixEnd_658536 16698543026634109065257 := by
  unfold tailWord_658536
  simp only [CollatzResearch.WordTrace]
  refine ⟨12009390571122007919897731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16012520761496010559863641 12009390571122007919897731)
  ·
    refine ⟨18014085856683011879846597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12009390571122007919897731 18014085856683011879846597)
    ·
      refine ⟨3377641098128064727471237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18014085856683011879846597 3377641098128064727471237)
      ·
        refine ⟨633307705899012136400857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3377641098128064727471237 633307705899012136400857)
        ·
          refine ⟨474980779424259102300643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 633307705899012136400857 474980779424259102300643)
          ·
            refine ⟨712471169136388653450965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474980779424259102300643 712471169136388653450965)
            ·
              refine ⟨16698543026634109065257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 712471169136388653450965 16698543026634109065257)
              ·
                rfl

theorem cell21_658536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 7].length) (baseStart_658536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658536 prefixEnd_658536 := by exact prefixLift 658536
  have htrace : WordTrace (prefixWord ++ tailWord_658536) baseStart_658536 baseEnd_658536 := by
    simpa [prefixWord, tailWord_658536, baseEnd_658536] using wordTrace_append hprefix tailTrace_658536
  have hstable : (prefixWord ++ tailWord_658536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658536).length < 2 ^ (prefixWord ++ tailWord_658536).sum := by decide
  have hdescent : baseEnd_658536 < baseStart_658536 := by decide
  rcases family_descends (prefixWord ++ tailWord_658536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658564 : List Nat := [2, 3, 2, 1, 2, 3, 1, 3, 4]
def baseStart_658564 : Nat := 118140960795 + 658564 * 2 ^ 59
def prefixEnd_658564 : Nat := 4983230072969 + 3 ^ 40 * 658564 * 2
def baseEnd_658564 : Nat := 150293277221185155120589

theorem tailTrace_658564 : CollatzResearch.WordTrace tailWord_658564 prefixEnd_658564 150293277221185155120589 := by
  unfold tailWord_658564
  simp only [CollatzResearch.WordTrace]
  refine ⟨12009901193071288310907373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16013201590761717747876497 12009901193071288310907373)
  ·
    refine ⟨4503712947401733116590265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12009901193071288310907373 4503712947401733116590265)
    ·
      refine ⟨3377784710551299837442699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4503712947401733116590265 3377784710551299837442699)
      ·
        refine ⟨5066677065826949756164049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3377784710551299837442699 5066677065826949756164049)
        ·
          refine ⟨3800007799370212317123037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5066677065826949756164049 3800007799370212317123037)
          ·
            refine ⟨1425002924763829618921139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3800007799370212317123037 1425002924763829618921139)
            ·
              refine ⟨2137504387145744428381709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425002924763829618921139 2137504387145744428381709)
              ·
                refine ⟨801564145179654160643141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2137504387145744428381709 801564145179654160643141)
                ·
                  refine ⟨150293277221185155120589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801564145179654160643141 150293277221185155120589)
                  ·
                    rfl

theorem cell21_658564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_658564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658564 prefixEnd_658564 := by exact prefixLift 658564
  have htrace : WordTrace (prefixWord ++ tailWord_658564) baseStart_658564 baseEnd_658564 := by
    simpa [prefixWord, tailWord_658564, baseEnd_658564] using wordTrace_append hprefix tailTrace_658564
  have hstable : (prefixWord ++ tailWord_658564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658564).length < 2 ^ (prefixWord ++ tailWord_658564).sum := by decide
  have hdescent : baseEnd_658564 < baseStart_658564 := by decide
  rcases family_descends (prefixWord ++ tailWord_658564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658578 : List Nat := [3, 2, 3, 1, 1, 2, 2, 7]
def baseStart_658578 : Nat := 118140960795 + 658578 * 2 ^ 59
def prefixEnd_658578 : Nat := 4983230072969 + 3 ^ 40 * 658578 * 2
def baseEnd_658578 : Nat := 50098824070641413962409

theorem tailTrace_658578 : CollatzResearch.WordTrace tailWord_658578 prefixEnd_658578 50098824070641413962409 := by
  unfold tailWord_658578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6005078252022964253206097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16013542005394571341882925 6005078252022964253206097)
  ·
    refine ⟨4503808689017223189904573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6005078252022964253206097 4503808689017223189904573)
    ·
      refine ⟨1688928258381458696214215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4503808689017223189904573 1688928258381458696214215)
      ·
        refine ⟨2533392387572188044321323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688928258381458696214215 2533392387572188044321323)
        ·
          refine ⟨3800088581358282066481985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533392387572188044321323 3800088581358282066481985)
          ·
            refine ⟨2850066436018711549861489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3800088581358282066481985 2850066436018711549861489)
            ·
              refine ⟨2137549827014033662396117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2850066436018711549861489 2137549827014033662396117)
              ·
                refine ⟨50098824070641413962409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2137549827014033662396117 50098824070641413962409)
                ·
                  rfl

theorem cell21_658578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_658578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658578 prefixEnd_658578 := by exact prefixLift 658578
  have htrace : WordTrace (prefixWord ++ tailWord_658578) baseStart_658578 baseEnd_658578 := by
    simpa [prefixWord, tailWord_658578, baseEnd_658578] using wordTrace_append hprefix tailTrace_658578
  have hstable : (prefixWord ++ tailWord_658578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658578).length < 2 ^ (prefixWord ++ tailWord_658578).sum := by decide
  have hdescent : baseEnd_658578 < baseStart_658578 := by decide
  rcases family_descends (prefixWord ++ tailWord_658578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658623 : List Nat := [1, 1, 2, 2, 2, 2, 4, 3, 4]
def baseStart_658623 : Nat := 118140960795 + 658623 * 2 ^ 59
def prefixEnd_658623 : Nat := 4983230072969 + 3 ^ 40 * 658623 * 2
def baseEnd_658623 : Nat := 150306741825014163637135

theorem tailTrace_658623 : CollatzResearch.WordTrace tailWord_658623 prefixEnd_658623 150306741825014163637135 := by
  unfold tailWord_658623
  simp only [CollatzResearch.WordTrace]
  refine ⟨24021954292928829698212523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16014636195285886465475015 24021954292928829698212523)
  ·
    refine ⟨36032931439393244547318785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24021954292928829698212523 36032931439393244547318785)
    ·
      refine ⟨27024698579544933410489089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36032931439393244547318785 27024698579544933410489089)
      ·
        refine ⟨20268523934658700057866817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27024698579544933410489089 20268523934658700057866817)
        ·
          refine ⟨15201392950994025043400113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20268523934658700057866817 15201392950994025043400113)
          ·
            refine ⟨11401044713245518782550085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15201392950994025043400113 11401044713245518782550085)
            ·
              refine ⟨2137695883733534771728141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11401044713245518782550085 2137695883733534771728141)
              ·
                refine ⟨801635956400075539398053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2137695883733534771728141 801635956400075539398053)
                ·
                  refine ⟨150306741825014163637135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801635956400075539398053 150306741825014163637135)
                  ·
                    rfl

theorem cell21_658623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 4].length) (baseStart_658623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658623 prefixEnd_658623 := by exact prefixLift 658623
  have htrace : WordTrace (prefixWord ++ tailWord_658623) baseStart_658623 baseEnd_658623 := by
    simpa [prefixWord, tailWord_658623, baseEnd_658623] using wordTrace_append hprefix tailTrace_658623
  have hstable : (prefixWord ++ tailWord_658623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658623).length < 2 ^ (prefixWord ++ tailWord_658623).sum := by decide
  have hdescent : baseEnd_658623 < baseStart_658623 := by decide
  rcases family_descends (prefixWord ++ tailWord_658623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658668 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 5]
def baseStart_658668 : Nat := 118140960795 + 658668 * 2 ^ 59
def prefixEnd_658668 : Nat := 4983230072969 + 3 ^ 40 * 658668 * 2
def baseEnd_658668 : Nat := 150317011438104085387043

theorem tailTrace_658668 : CollatzResearch.WordTrace tailWord_658668 prefixEnd_658668 150317011438104085387043 := by
  unfold tailWord_658668
  simp only [CollatzResearch.WordTrace]
  refine ⟨12011797788882901191800329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16015730385177201589067105 12011797788882901191800329)
  ·
    refine ⟨9008848341662175893850247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12011797788882901191800329 9008848341662175893850247)
    ·
      refine ⟨13513272512493263840775371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9008848341662175893850247 13513272512493263840775371)
      ·
        refine ⟨20269908768739895761163057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13513272512493263840775371 20269908768739895761163057)
        ·
          refine ⟨15202431576554921820872293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20269908768739895761163057 15202431576554921820872293)
          ·
            refine ⟨2850455920604047841413555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15202431576554921820872293 2850455920604047841413555)
            ·
              refine ⟨4275683880906071762120333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2850455920604047841413555 4275683880906071762120333)
              ·
                refine ⟨1603381455339776910795125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4275683880906071762120333 1603381455339776910795125)
                ·
                  refine ⟨150317011438104085387043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1603381455339776910795125 150317011438104085387043)
                  ·
                    rfl

theorem cell21_658668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_658668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658668 prefixEnd_658668 := by exact prefixLift 658668
  have htrace : WordTrace (prefixWord ++ tailWord_658668) baseStart_658668 baseEnd_658668 := by
    simpa [prefixWord, tailWord_658668, baseEnd_658668] using wordTrace_append hprefix tailTrace_658668
  have hstable : (prefixWord ++ tailWord_658668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658668).length < 2 ^ (prefixWord ++ tailWord_658668).sum := by decide
  have hdescent : baseEnd_658668 < baseStart_658668 := by decide
  rcases family_descends (prefixWord ++ tailWord_658668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658702 : List Nat := [4, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_658702 : Nat := 118140960795 + 658702 * 2 ^ 59
def prefixEnd_658702 : Nat := 4983230072969 + 3 ^ 40 * 658702 * 2
def baseEnd_658702 : Nat := 150324770701327581820307

theorem tailTrace_658702 : CollatzResearch.WordTrace tailWord_658702 prefixEnd_658702 150324770701327581820307 := by
  unfold tailWord_658702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3003104457455328273792295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16016557106428417460225573 3003104457455328273792295)
  ·
    refine ⟨4504656686182992410688443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3003104457455328273792295 4504656686182992410688443)
    ·
      refine ⟨6756985029274488616032665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4504656686182992410688443 6756985029274488616032665)
      ·
        refine ⟨5067738771955866462024499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6756985029274488616032665 5067738771955866462024499)
        ·
          refine ⟨7601608157933799693036749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5067738771955866462024499 7601608157933799693036749)
          ·
            refine ⟨2850603059225174884888781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7601608157933799693036749 2850603059225174884888781)
            ·
              refine ⟨1068976147209440581833293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2850603059225174884888781 1068976147209440581833293)
              ·
                refine ⟨400866055203540218187485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1068976147209440581833293 400866055203540218187485)
                ·
                  refine ⟨150324770701327581820307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400866055203540218187485 150324770701327581820307)
                  ·
                    rfl

theorem cell21_658702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_658702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658702 prefixEnd_658702 := by exact prefixLift 658702
  have htrace : WordTrace (prefixWord ++ tailWord_658702) baseStart_658702 baseEnd_658702 := by
    simpa [prefixWord, tailWord_658702, baseEnd_658702] using wordTrace_append hprefix tailTrace_658702
  have hstable : (prefixWord ++ tailWord_658702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658702).length < 2 ^ (prefixWord ++ tailWord_658702).sum := by decide
  have hdescent : baseEnd_658702 < baseStart_658702 := by decide
  rcases family_descends (prefixWord ++ tailWord_658702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658719 : List Nat := [1, 1, 2, 4, 4, 1, 3, 2, 3]
def baseStart_658719 : Nat := 118140960795 + 658719 * 2 ^ 59
def prefixEnd_658719 : Nat := 4983230072969 + 3 ^ 40 * 658719 * 2
def baseEnd_658719 : Nat := 150328650332939330036939

theorem tailTrace_658719 : CollatzResearch.WordTrace tailWord_658719 prefixEnd_658719 150328650332939330036939 := by
  unfold tailWord_658719
  simp only [CollatzResearch.WordTrace]
  refine ⟨24025455700581038093707211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16016970467054025395804807 24025455700581038093707211)
  ·
    refine ⟨36038183550871557140560817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24025455700581038093707211 36038183550871557140560817)
    ·
      refine ⟨27028637663153667855420613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36038183550871557140560817 27028637663153667855420613)
      ·
        refine ⟨5067869561841312722891365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27028637663153667855420613 5067869561841312722891365)
        ·
          refine ⟨950225542845246135542131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5067869561841312722891365 950225542845246135542131)
          ·
            refine ⟨1425338314267869203313197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950225542845246135542131 1425338314267869203313197)
            ·
              refine ⟨534501867850450951242449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1425338314267869203313197 534501867850450951242449)
              ·
                refine ⟨400876400887838213431837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534501867850450951242449 400876400887838213431837)
                ·
                  refine ⟨150328650332939330036939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400876400887838213431837 150328650332939330036939)
                  ·
                    rfl

theorem cell21_658719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 3].length) (baseStart_658719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658719 prefixEnd_658719 := by exact prefixLift 658719
  have htrace : WordTrace (prefixWord ++ tailWord_658719) baseStart_658719 baseEnd_658719 := by
    simpa [prefixWord, tailWord_658719, baseEnd_658719] using wordTrace_append hprefix tailTrace_658719
  have hstable : (prefixWord ++ tailWord_658719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658719).length < 2 ^ (prefixWord ++ tailWord_658719).sum := by decide
  have hdescent : baseEnd_658719 < baseStart_658719 := by decide
  rcases family_descends (prefixWord ++ tailWord_658719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658730 : List Nat := [3, 1, 4, 2, 1, 1, 1, 8]
def baseStart_658730 : Nat := 118140960795 + 658730 * 2 ^ 59
def prefixEnd_658730 : Nat := 4983230072969 + 3 ^ 40 * 658730 * 2
def baseEnd_658730 : Nat := 50110386894268585117861

theorem tailTrace_658730 : CollatzResearch.WordTrace tailWord_658730 prefixEnd_658730 50110386894268585117861 := by
  unfold tailWord_658730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6006464225885296743089411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16017237935694124648238429 6006464225885296743089411)
  ·
    refine ⟨9009696338827945114634117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6006464225885296743089411 9009696338827945114634117)
    ·
      refine ⟨1689318063530239708993897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9009696338827945114634117 1689318063530239708993897)
      ·
        refine ⟨1266988547647679781745423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1689318063530239708993897 1266988547647679781745423)
        ·
          refine ⟨1900482821471519672618135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266988547647679781745423 1900482821471519672618135)
          ·
            refine ⟨2850724232207279508927203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1900482821471519672618135 2850724232207279508927203)
            ·
              refine ⟨4276086348310919263390805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2850724232207279508927203 4276086348310919263390805)
              ·
                refine ⟨50110386894268585117861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4276086348310919263390805 50110386894268585117861)
                ·
                  rfl

theorem cell21_658730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_658730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658730 prefixEnd_658730 := by exact prefixLift 658730
  have htrace : WordTrace (prefixWord ++ tailWord_658730) baseStart_658730 baseEnd_658730 := by
    simpa [prefixWord, tailWord_658730, baseEnd_658730] using wordTrace_append hprefix tailTrace_658730
  have hstable : (prefixWord ++ tailWord_658730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658730).length < 2 ^ (prefixWord ++ tailWord_658730).sum := by decide
  have hdescent : baseEnd_658730 < baseStart_658730 := by decide
  rcases family_descends (prefixWord ++ tailWord_658730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658733 : List Nat := [1, 5, 3, 1, 1, 2, 1, 3, 4]
def baseStart_658733 : Nat := 118140960795 + 658733 * 2 ^ 59
def prefixEnd_658733 : Nat := 4983230072969 + 3 ^ 40 * 658733 * 2
def baseEnd_658733 : Nat := 150331845323678416803577

theorem tailTrace_658733 : CollatzResearch.WordTrace tailWord_658733 prefixEnd_658733 150331845323678416803577 := by
  unfold tailWord_658733
  simp only [CollatzResearch.WordTrace]
  refine ⟨24025966322530318484716853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16017310881686878989811235 24025966322530318484716853)
  ·
    refine ⟨2252434342737217357942205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24025966322530318484716853 2252434342737217357942205)
    ·
      refine ⟨844662878526456509228327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2252434342737217357942205 844662878526456509228327)
      ·
        refine ⟨1266994317789684763842491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844662878526456509228327 1266994317789684763842491)
        ·
          refine ⟨1900491476684527145763737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266994317789684763842491 1900491476684527145763737)
          ·
            refine ⟨1425368607513395359322803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1900491476684527145763737 1425368607513395359322803)
            ·
              refine ⟨2138052911270093038984205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425368607513395359322803 2138052911270093038984205)
              ·
                refine ⟨801769841726284889619077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2138052911270093038984205 801769841726284889619077)
                ·
                  refine ⟨150331845323678416803577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801769841726284889619077 150331845323678416803577)
                  ·
                    rfl

theorem cell21_658733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_658733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658733 prefixEnd_658733 := by exact prefixLift 658733
  have htrace : WordTrace (prefixWord ++ tailWord_658733) baseStart_658733 baseEnd_658733 := by
    simpa [prefixWord, tailWord_658733, baseEnd_658733] using wordTrace_append hprefix tailTrace_658733
  have hstable : (prefixWord ++ tailWord_658733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658733).length < 2 ^ (prefixWord ++ tailWord_658733).sum := by decide
  have hdescent : baseEnd_658733 < baseStart_658733 := by decide
  rcases family_descends (prefixWord ++ tailWord_658733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658775 : List Nat := [1, 1, 3, 2, 3, 2, 1, 4, 4]
def baseStart_658775 : Nat := 118140960795 + 658775 * 2 ^ 59
def prefixEnd_658775 : Nat := 4983230072969 + 3 ^ 40 * 658775 * 2
def baseEnd_658775 : Nat := 150341430295895677103491

theorem tailTrace_658775 : CollatzResearch.WordTrace tailWord_658775 prefixEnd_658775 150341430295895677103491 := by
  unfold tailWord_658775
  simp only [CollatzResearch.WordTrace]
  refine ⟨24027498188378159657745779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16018332125585439771830519 24027498188378159657745779)
  ·
    refine ⟨36041247282567239486618669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24027498188378159657745779 36041247282567239486618669)
    ·
      refine ⟨13515467730962714807482001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36041247282567239486618669 13515467730962714807482001)
      ·
        refine ⟨10136600798222036105611501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13515467730962714807482001 10136600798222036105611501)
        ·
          refine ⟨3801225299333263539604313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10136600798222036105611501 3801225299333263539604313)
          ·
            refine ⟨2850918974499947654703235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3801225299333263539604313 2850918974499947654703235)
            ·
              refine ⟨4276378461749921482054853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2850918974499947654703235 4276378461749921482054853)
              ·
                refine ⟨801820961578110277885285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4276378461749921482054853 801820961578110277885285)
                ·
                  refine ⟨150341430295895677103491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801820961578110277885285 150341430295895677103491)
                  ·
                    rfl

theorem cell21_658775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 4].length) (baseStart_658775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658775 prefixEnd_658775 := by exact prefixLift 658775
  have htrace : WordTrace (prefixWord ++ tailWord_658775) baseStart_658775 baseEnd_658775 := by
    simpa [prefixWord, tailWord_658775, baseEnd_658775] using wordTrace_append hprefix tailTrace_658775
  have hstable : (prefixWord ++ tailWord_658775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658775).length < 2 ^ (prefixWord ++ tailWord_658775).sum := by decide
  have hdescent : baseEnd_658775 < baseStart_658775 := by decide
  rcases family_descends (prefixWord ++ tailWord_658775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658778 : List Nat := [3, 1, 1, 2, 1, 2, 6, 2, 3]
def baseStart_658778 : Nat := 118140960795 + 658778 * 2 ^ 59
def prefixEnd_658778 : Nat := 4983230072969 + 3 ^ 40 * 658778 * 2
def baseEnd_658778 : Nat := 150342114936768338553485

theorem tailTrace_658778 : CollatzResearch.WordTrace tailWord_658778 prefixEnd_658778 150342114936768338553485 := by
  unfold tailWord_658778
  simp only [CollatzResearch.WordTrace]
  refine ⟨6006901901841822792526247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16018405071578194113403325 6006901901841822792526247)
  ·
    refine ⟨9010352852762734188789371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6006901901841822792526247 9010352852762734188789371)
    ·
      refine ⟨13515529279144101283184057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9010352852762734188789371 13515529279144101283184057)
      ·
        refine ⟨10136646959358075962388043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13515529279144101283184057 10136646959358075962388043)
        ·
          refine ⟨15204970439037113943582065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10136646959358075962388043 15204970439037113943582065)
          ·
            refine ⟨11403727829277835457686549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15204970439037113943582065 11403727829277835457686549)
            ·
              refine ⟨534549741997398537079057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11403727829277835457686549 534549741997398537079057)
              ·
                refine ⟨400912306498048902809293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534549741997398537079057 400912306498048902809293)
                ·
                  refine ⟨150342114936768338553485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400912306498048902809293 150342114936768338553485)
                  ·
                    rfl

theorem cell21_658778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_658778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658778 prefixEnd_658778 := by exact prefixLift 658778
  have htrace : WordTrace (prefixWord ++ tailWord_658778) baseStart_658778 baseEnd_658778 := by
    simpa [prefixWord, tailWord_658778, baseEnd_658778] using wordTrace_append hprefix tailTrace_658778
  have hstable : (prefixWord ++ tailWord_658778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658778).length < 2 ^ (prefixWord ++ tailWord_658778).sum := by decide
  have hdescent : baseEnd_658778 < baseStart_658778 := by decide
  rcases family_descends (prefixWord ++ tailWord_658778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658781 : List Nat := [1, 4, 5, 1, 1, 2, 1, 6]
def baseStart_658781 : Nat := 118140960795 + 658781 * 2 ^ 59
def prefixEnd_658781 : Nat := 4983230072969 + 3 ^ 40 * 658781 * 2
def baseEnd_658781 : Nat := 50114266525880333334493

theorem tailTrace_658781 : CollatzResearch.WordTrace tailWord_658781 prefixEnd_658781 50114266525880333334493 := by
  unfold tailWord_658781
  simp only [CollatzResearch.WordTrace]
  refine ⟨24027717026356422682464197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16018478017570948454976131 24027717026356422682464197)
  ·
    refine ⟨4505196942441829252962037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24027717026356422682464197 4505196942441829252962037)
    ·
      refine ⟨422362213353921492465191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4505196942441829252962037 422362213353921492465191)
      ·
        refine ⟨633543320030882238697787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422362213353921492465191 633543320030882238697787)
        ·
          refine ⟨950314980046323358046681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633543320030882238697787 950314980046323358046681)
          ·
            refine ⟨712736235034742518535011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 950314980046323358046681 712736235034742518535011)
            ·
              refine ⟨1069104352552113777802517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712736235034742518535011 1069104352552113777802517)
              ·
                refine ⟨50114266525880333334493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1069104352552113777802517 50114266525880333334493)
                ·
                  rfl

theorem cell21_658781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 6].length) (baseStart_658781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658781 prefixEnd_658781 := by exact prefixLift 658781
  have htrace : WordTrace (prefixWord ++ tailWord_658781) baseStart_658781 baseEnd_658781 := by
    simpa [prefixWord, tailWord_658781, baseEnd_658781] using wordTrace_append hprefix tailTrace_658781
  have hstable : (prefixWord ++ tailWord_658781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658781).length < 2 ^ (prefixWord ++ tailWord_658781).sum := by decide
  have hdescent : baseEnd_658781 < baseStart_658781 := by decide
  rcases family_descends (prefixWord ++ tailWord_658781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658837 : List Nat := [1, 3, 2, 1, 1, 2, 4, 4, 3]
def baseStart_658837 : Nat := 118140960795 + 658837 * 2 ^ 59
def prefixEnd_658837 : Nat := 4983230072969 + 3 ^ 40 * 658837 * 2
def baseEnd_658837 : Nat := 150355579540597347070031

theorem tailTrace_658837 : CollatzResearch.WordTrace tailWord_658837 prefixEnd_658837 150355579540597347070031 := by
  unfold tailWord_658837
  simp only [CollatzResearch.WordTrace]
  refine ⟨24029759514153544246502765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16019839676102362831001843 24029759514153544246502765)
  ·
    refine ⟨9011159817807579092438537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24029759514153544246502765 9011159817807579092438537)
    ·
      refine ⟨6758369863355684319328903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9011159817807579092438537 6758369863355684319328903)
      ·
        refine ⟨10137554795033526478993355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6758369863355684319328903 10137554795033526478993355)
        ·
          refine ⟨15206332192550289718490033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10137554795033526478993355 15206332192550289718490033)
          ·
            refine ⟨11404749144412717288867525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15206332192550289718490033 11404749144412717288867525)
            ·
              refine ⟨2138390464577384491662661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11404749144412717288867525 2138390464577384491662661)
              ·
                refine ⟨400948212108259592186749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2138390464577384491662661 400948212108259592186749)
                ·
                  refine ⟨150355579540597347070031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400948212108259592186749 150355579540597347070031)
                  ·
                    rfl

theorem cell21_658837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_658837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658837 prefixEnd_658837 := by exact prefixLift 658837
  have htrace : WordTrace (prefixWord ++ tailWord_658837) baseStart_658837 baseEnd_658837 := by
    simpa [prefixWord, tailWord_658837, baseEnd_658837] using wordTrace_append hprefix tailTrace_658837
  have hstable : (prefixWord ++ tailWord_658837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658837).length < 2 ^ (prefixWord ++ tailWord_658837).sum := by decide
  have hdescent : baseEnd_658837 < baseStart_658837 := by decide
  rcases family_descends (prefixWord ++ tailWord_658837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658865 : List Nat := [1, 2, 2, 4, 1, 1, 3, 7]
def baseStart_658865 : Nat := 118140960795 + 658865 * 2 ^ 59
def prefixEnd_658865 : Nat := 4983230072969 + 3 ^ 40 * 658865 * 2
def baseEnd_658865 : Nat := 50120656507358506867769

theorem tailTrace_658865 : CollatzResearch.WordTrace tailWord_658865 prefixEnd_658865 50120656507358506867769 := by
  unfold tailWord_658865
  simp only [CollatzResearch.WordTrace]
  refine ⟨24030780758052105028522049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16020520505368070019014699 24030780758052105028522049)
  ·
    refine ⟨18023085568539078771391537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24030780758052105028522049 18023085568539078771391537)
    ·
      refine ⟨13517314176404309078543653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18023085568539078771391537 13517314176404309078543653)
      ·
        refine ⟨2534496408075807952226935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13517314176404309078543653 2534496408075807952226935)
        ·
          refine ⟨3801744612113711928340403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2534496408075807952226935 3801744612113711928340403)
          ·
            refine ⟨5702616918170567892510605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3801744612113711928340403 5702616918170567892510605)
            ·
              refine ⟨2138481344313962959691477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5702616918170567892510605 2138481344313962959691477)
              ·
                refine ⟨50120656507358506867769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2138481344313962959691477 50120656507358506867769)
                ·
                  rfl

theorem cell21_658865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 7].length) (baseStart_658865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658865 prefixEnd_658865 := by exact prefixLift 658865
  have htrace : WordTrace (prefixWord ++ tailWord_658865) baseStart_658865 baseEnd_658865 := by
    simpa [prefixWord, tailWord_658865, baseEnd_658865] using wordTrace_append hprefix tailTrace_658865
  have hstable : (prefixWord ++ tailWord_658865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658865).length < 2 ^ (prefixWord ++ tailWord_658865).sum := by decide
  have hdescent : baseEnd_658865 < baseStart_658865 := by decide
  rcases family_descends (prefixWord ++ tailWord_658865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658879 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 7]
def baseStart_658879 : Nat := 118140960795 + 658879 * 2 ^ 59
def prefixEnd_658879 : Nat := 4983230072969 + 3 ^ 40 * 658879 * 2
def baseEnd_658879 : Nat := 150365164512814607369945

theorem tailTrace_658879 : CollatzResearch.WordTrace tailWord_658879 prefixEnd_658879 150365164512814607369945 := by
  unfold tailWord_658879
  simp only [CollatzResearch.WordTrace]
  refine ⟨24031291380001385419531691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16020860920000923613021127 24031291380001385419531691)
  ·
    refine ⟨36046937070002078129297537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24031291380001385419531691 36046937070002078129297537)
    ·
      refine ⟨27035202802501558596973153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36046937070002078129297537 27035202802501558596973153)
      ·
        refine ⟨20276402101876168947729865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27035202802501558596973153 20276402101876168947729865)
        ·
          refine ⟨15207301576407126710797399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20276402101876168947729865 15207301576407126710797399)
          ·
            refine ⟨22810952364610690066196099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15207301576407126710797399 22810952364610690066196099)
            ·
              refine ⟨34216428546916035099294149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22810952364610690066196099 34216428546916035099294149)
              ·
                refine ⟨6415580352546756581117653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34216428546916035099294149 6415580352546756581117653)
                ·
                  refine ⟨150365164512814607369945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6415580352546756581117653 150365164512814607369945)
                  ·
                    rfl

theorem cell21_658879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_658879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658879 prefixEnd_658879 := by exact prefixLift 658879
  have htrace : WordTrace (prefixWord ++ tailWord_658879) baseStart_658879 baseEnd_658879 := by
    simpa [prefixWord, tailWord_658879, baseEnd_658879] using wordTrace_append hprefix tailTrace_658879
  have hstable : (prefixWord ++ tailWord_658879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658879).length < 2 ^ (prefixWord ++ tailWord_658879).sum := by decide
  have hdescent : baseEnd_658879 < baseStart_658879 := by decide
  rcases family_descends (prefixWord ++ tailWord_658879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658902 : List Nat := [5, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_658902 : Nat := 118140960795 + 658902 * 2 ^ 59
def prefixEnd_658902 : Nat := 4983230072969 + 3 ^ 40 * 658902 * 2
def baseEnd_658902 : Nat := 150370413426171678486565

theorem tailTrace_658902 : CollatzResearch.WordTrace tailWord_658902 prefixEnd_658902 150370413426171678486565 := by
  unfold tailWord_658902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1502008141182378771726185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16021420172612040231745973 1502008141182378771726185)
  ·
    refine ⟨1126506105886784078794639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1502008141182378771726185 1126506105886784078794639)
    ·
      refine ⟨1689759158830176118191959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1126506105886784078794639 1689759158830176118191959)
      ·
        refine ⟨2534638738245264177287939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1689759158830176118191959 2534638738245264177287939)
        ·
          refine ⟨3801958107367896265931909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2534638738245264177287939 3801958107367896265931909)
          ·
            refine ⟨712867145131480549862233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3801958107367896265931909 712867145131480549862233)
            ·
              refine ⟨534650358848610412396675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712867145131480549862233 534650358848610412396675)
              ·
                refine ⟨801975538272915618595013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534650358848610412396675 801975538272915618595013)
                ·
                  refine ⟨150370413426171678486565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801975538272915618595013 150370413426171678486565)
                  ·
                    rfl

theorem cell21_658902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_658902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658902 prefixEnd_658902 := by exact prefixLift 658902
  have htrace : WordTrace (prefixWord ++ tailWord_658902) baseStart_658902 baseEnd_658902 := by
    simpa [prefixWord, tailWord_658902, baseEnd_658902] using wordTrace_append hprefix tailTrace_658902
  have hstable : (prefixWord ++ tailWord_658902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658902).length < 2 ^ (prefixWord ++ tailWord_658902).sum := by decide
  have hdescent : baseEnd_658902 < baseStart_658902 := by decide
  rcases family_descends (prefixWord ++ tailWord_658902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658950 : List Nat := [6, 2, 1, 1, 3, 1, 1, 6]
def baseStart_658950 : Nat := 118140960795 + 658950 * 2 ^ 59
def prefixEnd_658950 : Nat := 4983230072969 + 3 ^ 40 * 658950 * 2
def baseEnd_658950 : Nat := 50127122560044753895489

theorem tailTrace_658950 : CollatzResearch.WordTrace tailWord_658950 prefixEnd_658950 50127122560044753895489 := by
  unfold tailWord_658950
  simp only [CollatzResearch.WordTrace]
  refine ⟨751058780085755142042697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16022587308496109696910869 751058780085755142042697)
  ·
    refine ⟨563294085064316356532023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 751058780085755142042697 563294085064316356532023)
    ·
      refine ⟨844941127596474534798035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 563294085064316356532023 844941127596474534798035)
      ·
        refine ⟨1267411691394711802197053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844941127596474534798035 1267411691394711802197053)
        ·
          refine ⟨475279384273016925823895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1267411691394711802197053 475279384273016925823895)
          ·
            refine ⟨712919076409525388735843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475279384273016925823895 712919076409525388735843)
            ·
              refine ⟨1069378614614288083103765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712919076409525388735843 1069378614614288083103765)
              ·
                refine ⟨50127122560044753895489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1069378614614288083103765 50127122560044753895489)
                ·
                  rfl

theorem cell21_658950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_658950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658950 prefixEnd_658950 := by exact prefixLift 658950
  have htrace : WordTrace (prefixWord ++ tailWord_658950) baseStart_658950 baseEnd_658950 := by
    simpa [prefixWord, tailWord_658950, baseEnd_658950] using wordTrace_append hprefix tailTrace_658950
  have hstable : (prefixWord ++ tailWord_658950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658950).length < 2 ^ (prefixWord ++ tailWord_658950).sum := by decide
  have hdescent : baseEnd_658950 < baseStart_658950 := by decide
  rcases family_descends (prefixWord ++ tailWord_658950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658972 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 5]
def baseStart_658972 : Nat := 118140960795 + 658972 * 2 ^ 59
def prefixEnd_658972 : Nat := 4983230072969 + 3 ^ 40 * 658972 * 2
def baseEnd_658972 : Nat := 150386388379867112319755

theorem tailTrace_658972 : CollatzResearch.WordTrace tailWord_658972 prefixEnd_658972 150386388379867112319755 := by
  unfold tailWord_658972
  simp only [CollatzResearch.WordTrace]
  refine ⟨12017341684332231151333585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16023122245776308201778113 12017341684332231151333585)
  ·
    refine ⟨9013006263249173363500189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12017341684332231151333585 9013006263249173363500189)
    ·
      refine ⟨3379877348718440011312571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9013006263249173363500189 3379877348718440011312571)
      ·
        refine ⟨5069816023077660016968857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3379877348718440011312571 5069816023077660016968857)
        ·
          refine ⟨3802362017308245012726643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5069816023077660016968857 3802362017308245012726643)
          ·
            refine ⟨5703543025962367519089965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3802362017308245012726643 5703543025962367519089965)
            ·
              refine ⟨2138828634735887819658737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5703543025962367519089965 2138828634735887819658737)
              ·
                refine ⟨1604121476051915864744053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2138828634735887819658737 1604121476051915864744053)
                ·
                  refine ⟨150386388379867112319755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1604121476051915864744053 150386388379867112319755)
                  ·
                    rfl

theorem cell21_658972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_658972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_658972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_658972 prefixEnd_658972 := by exact prefixLift 658972
  have htrace : WordTrace (prefixWord ++ tailWord_658972) baseStart_658972 baseEnd_658972 := by
    simpa [prefixWord, tailWord_658972, baseEnd_658972] using wordTrace_append hprefix tailTrace_658972
  have hstable : (prefixWord ++ tailWord_658972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658972).length < 2 ^ (prefixWord ++ tailWord_658972).sum := by decide
  have hdescent : baseEnd_658972 < baseStart_658972 := by decide
  rcases family_descends (prefixWord ++ tailWord_658972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659020 : List Nat := [2, 2, 1, 3, 1, 4, 3, 1, 4]
def baseStart_659020 : Nat := 118140960795 + 659020 * 2 ^ 59
def prefixEnd_659020 : Nat := 4983230072969 + 3 ^ 40 * 659020 * 2
def baseEnd_659020 : Nat := 150397342633829695519657

theorem tailTrace_659020 : CollatzResearch.WordTrace tailWord_659020 prefixEnd_659020 150397342633829695519657 := by
  unfold tailWord_659020
  simp only [CollatzResearch.WordTrace]
  refine ⟨12018217036245283250207257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16024289381660377666943009 12018217036245283250207257)
  ·
    refine ⟨9013662777183962437655443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12018217036245283250207257 9013662777183962437655443)
    ·
      refine ⟨13520494165775943656483165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9013662777183962437655443 13520494165775943656483165)
      ·
        refine ⟨5070185312165978871181187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13520494165775943656483165 5070185312165978871181187)
        ·
          refine ⟨7605277968248968306771781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5070185312165978871181187 7605277968248968306771781)
          ·
            refine ⟨1425989619046681557519709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7605277968248968306771781 1425989619046681557519709)
            ·
              refine ⟨534746107142505584069891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1425989619046681557519709 534746107142505584069891)
              ·
                refine ⟨802119160713758376104837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534746107142505584069891 802119160713758376104837)
                ·
                  refine ⟨150397342633829695519657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 802119160713758376104837 150397342633829695519657)
                  ·
                    rfl

theorem cell21_659020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_659020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659020 prefixEnd_659020 := by exact prefixLift 659020
  have htrace : WordTrace (prefixWord ++ tailWord_659020) baseStart_659020 baseEnd_659020 := by
    simpa [prefixWord, tailWord_659020, baseEnd_659020] using wordTrace_append hprefix tailTrace_659020
  have hstable : (prefixWord ++ tailWord_659020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659020).length < 2 ^ (prefixWord ++ tailWord_659020).sum := by decide
  have hdescent : baseEnd_659020 < baseStart_659020 := by decide
  rcases family_descends (prefixWord ++ tailWord_659020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659079 : List Nat := [1, 1, 4, 2, 1, 4, 1, 3, 4]
def baseStart_659079 : Nat := 118140960795 + 659079 * 2 ^ 59
def prefixEnd_659079 : Nat := 4983230072969 + 3 ^ 40 * 659079 * 2
def baseEnd_659079 : Nat := 150410807237658704036203

theorem tailTrace_659079 : CollatzResearch.WordTrace tailWord_659079 prefixEnd_659079 150410807237658704036203 := by
  unfold tailWord_659079
  simp only [CollatzResearch.WordTrace]
  refine ⟨24038585979276819576812291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16025723986184546384541527 24038585979276819576812291)
  ·
    refine ⟨36057878968915229365218437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24038585979276819576812291 36057878968915229365218437)
    ·
      refine ⟨6760852306671605505978457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36057878968915229365218437 6760852306671605505978457)
      ·
        refine ⟨5070639230003704129483843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6760852306671605505978457 5070639230003704129483843)
        ·
          refine ⟨7605958845005556194225765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5070639230003704129483843 7605958845005556194225765)
          ·
            refine ⟨1426117283438541786417331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7605958845005556194225765 1426117283438541786417331)
            ·
              refine ⟨2139175925157812679625997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426117283438541786417331 2139175925157812679625997)
              ·
                refine ⟨802190971934179754859749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2139175925157812679625997 802190971934179754859749)
                ·
                  refine ⟨150410807237658704036203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 802190971934179754859749 150410807237658704036203)
                  ·
                    rfl

theorem cell21_659079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 4].length) (baseStart_659079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659079 prefixEnd_659079 := by exact prefixLift 659079
  have htrace : WordTrace (prefixWord ++ tailWord_659079) baseStart_659079 baseEnd_659079 := by
    simpa [prefixWord, tailWord_659079, baseEnd_659079] using wordTrace_append hprefix tailTrace_659079
  have hstable : (prefixWord ++ tailWord_659079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659079).length < 2 ^ (prefixWord ++ tailWord_659079).sum := by decide
  have hdescent : baseEnd_659079 < baseStart_659079 := by decide
  rcases family_descends (prefixWord ++ tailWord_659079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659169 : List Nat := [1, 2, 3, 1, 5, 1, 8]
def baseStart_659169 : Nat := 118140960795 + 659169 * 2 ^ 59
def prefixEnd_659169 : Nat := 4983230072969 + 3 ^ 40 * 659169 * 2
def baseEnd_659169 : Nat := 16714594051537616392891

theorem tailTrace_659169 : CollatzResearch.WordTrace tailWord_659169 prefixEnd_659169 16714594051537616392891 := by
  unfold tailWord_659169
  simp only [CollatzResearch.WordTrace]
  refine ⟨24041868548950764947588561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16027912365967176631725707 24041868548950764947588561)
  ·
    refine ⟨18031401411713073710691421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24041868548950764947588561 18031401411713073710691421)
    ·
      refine ⟨6761775529392402641509283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18031401411713073710691421 6761775529392402641509283)
      ·
        refine ⟨10142663294088603962263925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6761775529392402641509283 10142663294088603962263925)
        ·
          refine ⟨950874683820806621462243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10142663294088603962263925 950874683820806621462243)
          ·
            refine ⟨1426312025731209932193365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950874683820806621462243 1426312025731209932193365)
            ·
              refine ⟨16714594051537616392891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1426312025731209932193365 16714594051537616392891)
              ·
                rfl

theorem cell21_659169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 8].length) (baseStart_659169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659169 prefixEnd_659169 := by exact prefixLift 659169
  have htrace : WordTrace (prefixWord ++ tailWord_659169) baseStart_659169 baseEnd_659169 := by
    simpa [prefixWord, tailWord_659169, baseEnd_659169] using wordTrace_append hprefix tailTrace_659169
  have hstable : (prefixWord ++ tailWord_659169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659169).length < 2 ^ (prefixWord ++ tailWord_659169).sum := by decide
  have hdescent : baseEnd_659169 < baseStart_659169 := by decide
  rcases family_descends (prefixWord ++ tailWord_659169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659214 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_659214 : Nat := 118140960795 + 659214 * 2 ^ 59
def prefixEnd_659214 : Nat := 4983230072969 + 3 ^ 40 * 659214 * 2
def baseEnd_659214 : Nat := 150441616076928469285927

theorem tailTrace_659214 : CollatzResearch.WordTrace tailWord_659214 prefixEnd_659214 150441616076928469285927 := by
  unfold tailWord_659214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3005438729223467204122087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16029006555858491755317797 3005438729223467204122087)
  ·
    refine ⟨4508158093835200806183131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3005438729223467204122087 4508158093835200806183131)
    ·
      refine ⟨6762237140752801209274697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4508158093835200806183131 6762237140752801209274697)
      ·
        refine ⟨5071677855564600906956023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6762237140752801209274697 5071677855564600906956023)
        ·
          refine ⟨7607516783346901360434035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5071677855564600906956023 7607516783346901360434035)
          ·
            refine ⟨11411275175020352040651053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7607516783346901360434035 11411275175020352040651053)
            ·
              refine ⟨4279228190632632015244145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11411275175020352040651053 4279228190632632015244145)
              ·
                refine ⟨3209421142974474011433109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4279228190632632015244145 3209421142974474011433109)
                ·
                  refine ⟨150441616076928469285927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3209421142974474011433109 150441616076928469285927)
                  ·
                    rfl

theorem cell21_659214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_659214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659214 prefixEnd_659214 := by exact prefixLift 659214
  have htrace : WordTrace (prefixWord ++ tailWord_659214) baseStart_659214 baseEnd_659214 := by
    simpa [prefixWord, tailWord_659214, baseEnd_659214] using wordTrace_append hprefix tailTrace_659214
  have hstable : (prefixWord ++ tailWord_659214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659214).length < 2 ^ (prefixWord ++ tailWord_659214).sum := by decide
  have hdescent : baseEnd_659214 < baseStart_659214 := by decide
  rcases family_descends (prefixWord ++ tailWord_659214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659220 : List Nat := [2, 4, 4, 1, 1, 2, 7]
def baseStart_659220 : Nat := 118140960795 + 659220 * 2 ^ 59
def prefixEnd_659220 : Nat := 4983230072969 + 3 ^ 40 * 659220 * 2
def baseEnd_659220 : Nat := 16715887262074865798435

theorem tailTrace_659220 : CollatzResearch.WordTrace tailWord_659220 prefixEnd_659220 16715887262074865798435 := by
  unfold tailWord_659220
  simp only [CollatzResearch.WordTrace]
  refine ⟨12021864335883000328847557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16029152447844000438463409 12021864335883000328847557)
  ·
    refine ⟨2254099562978062561658917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12021864335883000328847557 2254099562978062561658917)
    ·
      refine ⟨422643668058386730311047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2254099562978062561658917 422643668058386730311047)
      ·
        refine ⟨633965502087580095466571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422643668058386730311047 633965502087580095466571)
        ·
          refine ⟨950948253131370143199857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633965502087580095466571 950948253131370143199857)
          ·
            refine ⟨713211189848527607399893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 950948253131370143199857 713211189848527607399893)
            ·
              refine ⟨16715887262074865798435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 713211189848527607399893 16715887262074865798435)
              ·
                rfl

theorem cell21_659220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 7].length) (baseStart_659220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659220 prefixEnd_659220 := by exact prefixLift 659220
  have htrace : WordTrace (prefixWord ++ tailWord_659220) baseStart_659220 baseEnd_659220 := by
    simpa [prefixWord, tailWord_659220, baseEnd_659220] using wordTrace_append hprefix tailTrace_659220
  have hstable : (prefixWord ++ tailWord_659220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659220).length < 2 ^ (prefixWord ++ tailWord_659220).sum := by decide
  have hdescent : baseEnd_659220 < baseStart_659220 := by decide
  rcases family_descends (prefixWord ++ tailWord_659220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659234 : List Nat := [3, 3, 1, 1, 2, 1, 5, 2, 3]
def baseStart_659234 : Nat := 118140960795 + 659234 * 2 ^ 59
def prefixEnd_659234 : Nat := 4983230072969 + 3 ^ 40 * 659234 * 2
def baseEnd_659234 : Nat := 150446180349412878952553

theorem tailTrace_659234 : CollatzResearch.WordTrace tailWord_659234 prefixEnd_659234 150446180349412878952553 := by
  unfold tailWord_659234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6011059823428820262176189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16029492862476854032469837 6011059823428820262176189)
  ·
    refine ⟨2254147433785807598316071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6011059823428820262176189 2254147433785807598316071)
    ·
      refine ⟨3381221150678711397474107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2254147433785807598316071 3381221150678711397474107)
      ·
        refine ⟨5071831726018067096211161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3381221150678711397474107 5071831726018067096211161)
        ·
          refine ⟨3803873794513550322158371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5071831726018067096211161 3803873794513550322158371)
          ·
            refine ⟨5705810691770325483237557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3803873794513550322158371 5705810691770325483237557)
            ·
              refine ⟨534919752353468014053521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5705810691770325483237557 534919752353468014053521)
              ·
                refine ⟨401189814265101010540141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534919752353468014053521 401189814265101010540141)
                ·
                  refine ⟨150446180349412878952553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 401189814265101010540141 150446180349412878952553)
                  ·
                    rfl

theorem cell21_659234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_659234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659234 prefixEnd_659234 := by exact prefixLift 659234
  have htrace : WordTrace (prefixWord ++ tailWord_659234) baseStart_659234 baseEnd_659234 := by
    simpa [prefixWord, tailWord_659234, baseEnd_659234] using wordTrace_append hprefix tailTrace_659234
  have hstable : (prefixWord ++ tailWord_659234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659234).length < 2 ^ (prefixWord ++ tailWord_659234).sum := by decide
  have hdescent : baseEnd_659234 < baseStart_659234 := by decide
  rcases family_descends (prefixWord ++ tailWord_659234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659321 : List Nat := [1, 2, 1, 3, 2, 2, 5, 5]
def baseStart_659321 : Nat := 118140960795 + 659321 * 2 ^ 59
def prefixEnd_659321 : Nat := 4983230072969 + 3 ^ 40 * 659321 * 2
def baseEnd_659321 : Nat := 50155344978240020334125

theorem tailTrace_659321 : CollatzResearch.WordTrace tailWord_659321 prefixEnd_659321 50155344978240020334125 := by
  unfold tailWord_659321
  simp only [CollatzResearch.WordTrace]
  refine ⟨24047412444400094907121817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16031608296266729938081211 24047412444400094907121817)
  ·
    refine ⟨18035559333300071180341363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24047412444400094907121817 18035559333300071180341363)
    ·
      refine ⟨27053338999950106770512045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18035559333300071180341363 27053338999950106770512045)
      ·
        refine ⟨10145002124981290038942017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27053338999950106770512045 10145002124981290038942017)
        ·
          refine ⟨7608751593735967529206513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10145002124981290038942017 7608751593735967529206513)
          ·
            refine ⟨5706563695301975646904885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7608751593735967529206513 5706563695301975646904885)
            ·
              refine ⟨534990346434560216897333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5706563695301975646904885 534990346434560216897333)
              ·
                refine ⟨50155344978240020334125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 534990346434560216897333 50155344978240020334125)
                ·
                  rfl

theorem cell21_659321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 5].length) (baseStart_659321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659321 prefixEnd_659321 := by exact prefixLift 659321
  have htrace : WordTrace (prefixWord ++ tailWord_659321) baseStart_659321 baseEnd_659321 := by
    simpa [prefixWord, tailWord_659321, baseEnd_659321] using wordTrace_append hprefix tailTrace_659321
  have hstable : (prefixWord ++ tailWord_659321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659321).length < 2 ^ (prefixWord ++ tailWord_659321).sum := by decide
  have hdescent : baseEnd_659321 < baseStart_659321 := by decide
  rcases family_descends (prefixWord ++ tailWord_659321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659358 : List Nat := [4, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_659358 : Nat := 118140960795 + 659358 * 2 ^ 59
def prefixEnd_659358 : Nat := 4983230072969 + 3 ^ 40 * 659358 * 2
def baseEnd_659358 : Nat := 150474478838816218885633

theorem tailTrace_659358 : CollatzResearch.WordTrace tailWord_659358 prefixEnd_659358 150474478838816218885633 := by
  unfold tailWord_659358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3006095243158256278277341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16032507963510700150812485 3006095243158256278277341)
  ·
    refine ⟨1127285716184346104354003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3006095243158256278277341 1127285716184346104354003)
    ·
      refine ⟨1690928574276519156531005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1127285716184346104354003 1690928574276519156531005)
      ·
        refine ⟨634098215353694683699127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1690928574276519156531005 634098215353694683699127)
        ·
          refine ⟨951147323030542025548691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634098215353694683699127 951147323030542025548691)
          ·
            refine ⟨1426720984545813038323037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951147323030542025548691 1426720984545813038323037)
            ·
              refine ⟨535020369204679889371139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1426720984545813038323037 535020369204679889371139)
              ·
                refine ⟨802530553807019834056709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535020369204679889371139 802530553807019834056709)
                ·
                  refine ⟨150474478838816218885633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 802530553807019834056709 150474478838816218885633)
                  ·
                    rfl

theorem cell21_659358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_659358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659358 prefixEnd_659358 := by exact prefixLift 659358
  have htrace : WordTrace (prefixWord ++ tailWord_659358) baseStart_659358 baseEnd_659358 := by
    simpa [prefixWord, tailWord_659358, baseEnd_659358] using wordTrace_append hprefix tailTrace_659358
  have hstable : (prefixWord ++ tailWord_659358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659358).length < 2 ^ (prefixWord ++ tailWord_659358).sum := by decide
  have hdescent : baseEnd_659358 < baseStart_659358 := by decide
  rcases family_descends (prefixWord ++ tailWord_659358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659417 : List Nat := [1, 2, 1, 2, 7, 1, 2, 1, 4]
def baseStart_659417 : Nat := 118140960795 + 659417 * 2 ^ 59
def prefixEnd_659417 : Nat := 4983230072969 + 3 ^ 40 * 659417 * 2
def baseEnd_659417 : Nat := 150487943442645227402179

theorem tailTrace_659417 : CollatzResearch.WordTrace tailWord_659417 prefixEnd_659417 150487943442645227402179 := by
  unfold tailWord_659417
  simp only [CollatzResearch.WordTrace]
  refine ⟨24050913852052303302616505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16033942568034868868411003 24050913852052303302616505)
  ·
    refine ⟨18038185389039227476962379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24050913852052303302616505 18038185389039227476962379)
    ·
      refine ⟨27057278083558841215443569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18038185389039227476962379 27057278083558841215443569)
      ·
        refine ⟨20292958562669130911582677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27057278083558841215443569 20292958562669130911582677)
        ·
          refine ⟨475616216312557755740219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 20292958562669130911582677 475616216312557755740219)
          ·
            refine ⟨713424324468836633610329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475616216312557755740219 713424324468836633610329)
            ·
              refine ⟨535068243351627475207747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713424324468836633610329 535068243351627475207747)
              ·
                refine ⟨802602365027441212811621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535068243351627475207747 802602365027441212811621)
                ·
                  refine ⟨150487943442645227402179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 802602365027441212811621 150487943442645227402179)
                  ·
                    rfl

theorem cell21_659417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 4].length) (baseStart_659417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659417 prefixEnd_659417 := by exact prefixLift 659417
  have htrace : WordTrace (prefixWord ++ tailWord_659417) baseStart_659417 baseEnd_659417 := by
    simpa [prefixWord, tailWord_659417, baseEnd_659417] using wordTrace_append hprefix tailTrace_659417
  have hstable : (prefixWord ++ tailWord_659417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659417).length < 2 ^ (prefixWord ++ tailWord_659417).sum := by decide
  have hdescent : baseEnd_659417 < baseStart_659417 := by decide
  rcases family_descends (prefixWord ++ tailWord_659417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659487 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 5]
def baseStart_659487 : Nat := 118140960795 + 659487 * 2 ^ 59
def prefixEnd_659487 : Nat := 4983230072969 + 3 ^ 40 * 659487 * 2
def baseEnd_659487 : Nat := 150503918396340661235369

theorem tailTrace_659487 : CollatzResearch.WordTrace tailWord_659487 prefixEnd_659487 150503918396340661235369 := by
  unfold tailWord_659487
  simp only [CollatzResearch.WordTrace]
  refine ⟨24053466961798705257664715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16035644641199136838443143 24053466961798705257664715)
  ·
    refine ⟨36080200442698057886497073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24053466961798705257664715 36080200442698057886497073)
    ·
      refine ⟨27060150332023543414872805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36080200442698057886497073 27060150332023543414872805)
      ·
        refine ⟨5073778187254414390288651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27060150332023543414872805 5073778187254414390288651)
        ·
          refine ⟨7610667280881621585432977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5073778187254414390288651 7610667280881621585432977)
          ·
            refine ⟨5708000460661216189074733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7610667280881621585432977 5708000460661216189074733)
            ·
              refine ⟨2140500172747956070903025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5708000460661216189074733 2140500172747956070903025)
              ·
                refine ⟨1605375129560967053177269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140500172747956070903025 1605375129560967053177269)
                ·
                  refine ⟨150503918396340661235369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1605375129560967053177269 150503918396340661235369)
                  ·
                    rfl

theorem cell21_659487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 5].length) (baseStart_659487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659487 prefixEnd_659487 := by exact prefixLift 659487
  have htrace : WordTrace (prefixWord ++ tailWord_659487) baseStart_659487 baseEnd_659487 := by
    simpa [prefixWord, tailWord_659487, baseEnd_659487] using wordTrace_append hprefix tailTrace_659487
  have hstable : (prefixWord ++ tailWord_659487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659487).length < 2 ^ (prefixWord ++ tailWord_659487).sum := by decide
  have hdescent : baseEnd_659487 < baseStart_659487 := by decide
  rcases family_descends (prefixWord ++ tailWord_659487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659504 : List Nat := [2, 1, 1, 1, 2, 5, 1, 5, 3]
def baseStart_659504 : Nat := 118140960795 + 659504 * 2 ^ 59
def prefixEnd_659504 : Nat := 4983230072969 + 3 ^ 40 * 659504 * 2
def baseEnd_659504 : Nat := 150507798027952409452001

theorem tailTrace_659504 : CollatzResearch.WordTrace tailWord_659504 prefixEnd_659504 150507798027952409452001 := by
  unfold tailWord_659504
  simp only [CollatzResearch.WordTrace]
  refine ⟨12027043501368558580516783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16036058001824744774022377 12027043501368558580516783)
  ·
    refine ⟨18040565252052837870775175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12027043501368558580516783 18040565252052837870775175)
    ·
      refine ⟨27060847878079256806162763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18040565252052837870775175 27060847878079256806162763)
      ·
        refine ⟨40591271817118885209244145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27060847878079256806162763 40591271817118885209244145)
        ·
          refine ⟨30443453862839163906933109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40591271817118885209244145 30443453862839163906933109)
          ·
            refine ⟨2854073799641171616274979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30443453862839163906933109 2854073799641171616274979)
            ·
              refine ⟨4281110699461757424412469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2854073799641171616274979 4281110699461757424412469)
              ·
                refine ⟨401354128074539758538669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4281110699461757424412469 401354128074539758538669)
                ·
                  refine ⟨150507798027952409452001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 401354128074539758538669 150507798027952409452001)
                  ·
                    rfl

theorem cell21_659504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 3].length) (baseStart_659504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659504 prefixEnd_659504 := by exact prefixLift 659504
  have htrace : WordTrace (prefixWord ++ tailWord_659504) baseStart_659504 baseEnd_659504 := by
    simpa [prefixWord, tailWord_659504, baseEnd_659504] using wordTrace_append hprefix tailTrace_659504
  have hstable : (prefixWord ++ tailWord_659504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659504).length < 2 ^ (prefixWord ++ tailWord_659504).sum := by decide
  have hdescent : baseEnd_659504 < baseStart_659504 := by decide
  rcases family_descends (prefixWord ++ tailWord_659504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659521 : List Nat := [1, 2, 5, 1, 2, 1, 2, 4, 3]
def baseStart_659521 : Nat := 118140960795 + 659521 * 2 ^ 59
def prefixEnd_659521 : Nat := 4983230072969 + 3 ^ 40 * 659521 * 2
def baseEnd_659521 : Nat := 150511677659564157668633

theorem tailTrace_659521 : CollatzResearch.WordTrace tailWord_659521 prefixEnd_659521 150511677659564157668633 := by
  unfold tailWord_659521
  simp only [CollatzResearch.WordTrace]
  refine ⟨24054707043675529064402417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16036471362450352709601611 24054707043675529064402417)
  ·
    refine ⟨18041030282756646798301813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24054707043675529064402417 18041030282756646798301813)
    ·
      refine ⟨1691346589008435637340795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18041030282756646798301813 1691346589008435637340795)
      ·
        refine ⟨2537019883512653456011193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1691346589008435637340795 2537019883512653456011193)
        ·
          refine ⟨1902764912634490092008395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2537019883512653456011193 1902764912634490092008395)
          ·
            refine ⟨2854147368951735138012593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902764912634490092008395 2854147368951735138012593)
            ·
              refine ⟨2140610526713801353509445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2854147368951735138012593 2140610526713801353509445)
              ·
                refine ⟨401364473758837753783021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2140610526713801353509445 401364473758837753783021)
                ·
                  refine ⟨150511677659564157668633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 401364473758837753783021 150511677659564157668633)
                  ·
                    rfl

theorem cell21_659521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 3].length) (baseStart_659521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659521 prefixEnd_659521 := by exact prefixLift 659521
  have htrace : WordTrace (prefixWord ++ tailWord_659521) baseStart_659521 baseEnd_659521 := by
    simpa [prefixWord, tailWord_659521, baseEnd_659521] using wordTrace_append hprefix tailTrace_659521
  have hstable : (prefixWord ++ tailWord_659521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659521).length < 2 ^ (prefixWord ++ tailWord_659521).sum := by decide
  have hdescent : baseEnd_659521 < baseStart_659521 := by decide
  rcases family_descends (prefixWord ++ tailWord_659521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659580 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 5]
def baseStart_659580 : Nat := 118140960795 + 659580 * 2 ^ 59
def prefixEnd_659580 : Nat := 4983230072969 + 3 ^ 40 * 659580 * 2
def baseEnd_659580 : Nat := 150525142263393166185179

theorem tailTrace_659580 : CollatzResearch.WordTrace tailWord_659580 prefixEnd_659580 150525142263393166185179 := by
  unfold tailWord_659580
  simp only [CollatzResearch.WordTrace]
  refine ⟨12028429475230891070400097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16037905966974521427200129 12028429475230891070400097)
  ·
    refine ⟨9021322106423168302800073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12028429475230891070400097 9021322106423168302800073)
    ·
      refine ⟨6765991579817376227100055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9021322106423168302800073 6765991579817376227100055)
      ·
        refine ⟨10148987369726064340650083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6765991579817376227100055 10148987369726064340650083)
        ·
          refine ⟨15223481054589096510975125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10148987369726064340650083 15223481054589096510975125)
          ·
            refine ⟨713600674433863898951959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15223481054589096510975125 713600674433863898951959)
            ·
              refine ⟨1070401011650795848427939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713600674433863898951959 1070401011650795848427939)
              ·
                refine ⟨1605601517476193772641909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070401011650795848427939 1605601517476193772641909)
                ·
                  refine ⟨150525142263393166185179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1605601517476193772641909 150525142263393166185179)
                  ·
                    rfl

theorem cell21_659580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_659580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659580 prefixEnd_659580 := by exact prefixLift 659580
  have htrace : WordTrace (prefixWord ++ tailWord_659580) baseStart_659580 baseEnd_659580 := by
    simpa [prefixWord, tailWord_659580, baseEnd_659580] using wordTrace_append hprefix tailTrace_659580
  have hstable : (prefixWord ++ tailWord_659580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659580).length < 2 ^ (prefixWord ++ tailWord_659580).sum := by decide
  have hdescent : baseEnd_659580 < baseStart_659580 := by decide
  rcases family_descends (prefixWord ++ tailWord_659580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659687 : List Nat := [1, 1, 5, 3, 1, 1, 3, 2, 4]
def baseStart_659687 : Nat := 118140960795 + 659687 * 2 ^ 59
def prefixEnd_659687 : Nat := 4983230072969 + 3 ^ 40 * 659687 * 2
def baseEnd_659687 : Nat := 150549561121184757901627

theorem tailTrace_659687 : CollatzResearch.WordTrace tailWord_659687 prefixEnd_659687 150549561121184757901627 := by
  unfold tailWord_659687
  simp only [CollatzResearch.WordTrace]
  refine ⟨24060761561074139414945315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16040507707382759609963543 24060761561074139414945315)
  ·
    refine ⟨36091142341611209122417973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24060761561074139414945315 36091142341611209122417973)
    ·
      refine ⟨3383544594526050855226685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36091142341611209122417973 3383544594526050855226685)
      ·
        refine ⟨1268829222947269070710007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3383544594526050855226685 1268829222947269070710007)
        ·
          refine ⟨1903243834420903606065011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268829222947269070710007 1903243834420903606065011)
          ·
            refine ⟨2854865751631355409097517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903243834420903606065011 2854865751631355409097517)
            ·
              refine ⟨1070574656861758278411569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2854865751631355409097517 1070574656861758278411569)
              ·
                refine ⟨802930992646318708808677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1070574656861758278411569 802930992646318708808677)
                ·
                  refine ⟨150549561121184757901627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 802930992646318708808677 150549561121184757901627)
                  ·
                    rfl

theorem cell21_659687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 4].length) (baseStart_659687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659687 prefixEnd_659687 := by exact prefixLift 659687
  have htrace : WordTrace (prefixWord ++ tailWord_659687) baseStart_659687 baseEnd_659687 := by
    simpa [prefixWord, tailWord_659687, baseEnd_659687] using wordTrace_append hprefix tailTrace_659687
  have hstable : (prefixWord ++ tailWord_659687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659687).length < 2 ^ (prefixWord ++ tailWord_659687).sum := by decide
  have hdescent : baseEnd_659687 < baseStart_659687 := by decide
  rcases family_descends (prefixWord ++ tailWord_659687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659729 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 6]
def baseStart_659729 : Nat := 118140960795 + 659729 * 2 ^ 59
def prefixEnd_659729 : Nat := 4983230072969 + 3 ^ 40 * 659729 * 2
def baseEnd_659729 : Nat := 150559146093402018201541

theorem tailTrace_659729 : CollatzResearch.WordTrace tailWord_659729 prefixEnd_659729 150559146093402018201541 := by
  unfold tailWord_659729
  simp only [CollatzResearch.WordTrace]
  refine ⟨24062293426921980587974241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16041528951281320391982827 24062293426921980587974241)
  ·
    refine ⟨18046720070191485440980681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24062293426921980587974241 18046720070191485440980681)
    ·
      refine ⟨13535040052643614080735511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18046720070191485440980681 13535040052643614080735511)
      ·
        refine ⟨20302560078965421121103267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13535040052643614080735511 20302560078965421121103267)
        ·
          refine ⟨30453840118448131681654901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20302560078965421121103267 30453840118448131681654901)
          ·
            refine ⟨2855047511104512345155147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30453840118448131681654901 2855047511104512345155147)
            ·
              refine ⟨4282571266656768517732721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2855047511104512345155147 4282571266656768517732721)
              ·
                refine ⟨3211928449992576388299541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4282571266656768517732721 3211928449992576388299541)
                ·
                  refine ⟨150559146093402018201541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3211928449992576388299541 150559146093402018201541)
                  ·
                    rfl

theorem cell21_659729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_659729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659729 prefixEnd_659729 := by exact prefixLift 659729
  have htrace : WordTrace (prefixWord ++ tailWord_659729) baseStart_659729 baseEnd_659729 := by
    simpa [prefixWord, tailWord_659729, baseEnd_659729] using wordTrace_append hprefix tailTrace_659729
  have hstable : (prefixWord ++ tailWord_659729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659729).length < 2 ^ (prefixWord ++ tailWord_659729).sum := by decide
  have hdescent : baseEnd_659729 < baseStart_659729 := by decide
  rcases family_descends (prefixWord ++ tailWord_659729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659746 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_659746 : Nat := 118140960795 + 659746 * 2 ^ 59
def prefixEnd_659746 : Nat := 4983230072969 + 3 ^ 40 * 659746 * 2
def baseEnd_659746 : Nat := 150563025725013766418173

theorem tailTrace_659746 : CollatzResearch.WordTrace tailWord_659746 prefixEnd_659746 150563025725013766418173 := by
  unfold tailWord_659746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6015728366965098122835773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16041942311906928327562061 6015728366965098122835773)
  ·
    refine ⟨2255898137611911796063415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6015728366965098122835773 2255898137611911796063415)
    ·
      refine ⟨3383847206417867694095123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2255898137611911796063415 3383847206417867694095123)
      ·
        refine ⟨5075770809626801541142685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3383847206417867694095123 5075770809626801541142685)
        ·
          refine ⟨1903414053610050577928507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5075770809626801541142685 1903414053610050577928507)
          ·
            refine ⟨2855121080415075866892761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903414053610050577928507 2855121080415075866892761)
            ·
              refine ⟨2141340810311306900169571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2855121080415075866892761 2141340810311306900169571)
              ·
                refine ⟨3212011215466960350254357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2141340810311306900169571 3212011215466960350254357)
                ·
                  refine ⟨150563025725013766418173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3212011215466960350254357 150563025725013766418173)
                  ·
                    rfl

theorem cell21_659746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_659746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659746 prefixEnd_659746 := by exact prefixLift 659746
  have htrace : WordTrace (prefixWord ++ tailWord_659746) baseStart_659746 baseEnd_659746 := by
    simpa [prefixWord, tailWord_659746, baseEnd_659746] using wordTrace_append hprefix tailTrace_659746
  have hstable : (prefixWord ++ tailWord_659746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659746).length < 2 ^ (prefixWord ++ tailWord_659746).sum := by decide
  have hdescent : baseEnd_659746 < baseStart_659746 := by decide
  rcases family_descends (prefixWord ++ tailWord_659746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659749 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 5]
def baseStart_659749 : Nat := 118140960795 + 659749 * 2 ^ 59
def prefixEnd_659749 : Nat := 4983230072969 + 3 ^ 40 * 659749 * 2
def baseEnd_659749 : Nat := 150563710365886427868167

theorem tailTrace_659749 : CollatzResearch.WordTrace tailWord_659749 prefixEnd_659749 150563710365886427868167 := by
  unfold tailWord_659749
  simp only [CollatzResearch.WordTrace]
  refine ⟨24063022886849524003702301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16042015257899682669134867 24063022886849524003702301)
  ·
    refine ⟨9023633582568571501388363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24063022886849524003702301 9023633582568571501388363)
    ·
      refine ⟨13535450373852857252082545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9023633582568571501388363 13535450373852857252082545)
      ·
        refine ⟨10151587780389642939061909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13535450373852857252082545 10151587780389642939061909)
        ·
          refine ⟨475855677205764512768527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10151587780389642939061909 475855677205764512768527)
          ·
            refine ⟨713783515808646769152791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475855677205764512768527 713783515808646769152791)
            ·
              refine ⟨1070675273712970153729187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713783515808646769152791 1070675273712970153729187)
              ·
                refine ⟨1606012910569455230593781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070675273712970153729187 1606012910569455230593781)
                ·
                  refine ⟨150563710365886427868167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1606012910569455230593781 150563710365886427868167)
                  ·
                    rfl

theorem cell21_659749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_659749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659749 prefixEnd_659749 := by exact prefixLift 659749
  have htrace : WordTrace (prefixWord ++ tailWord_659749) baseStart_659749 baseEnd_659749 := by
    simpa [prefixWord, tailWord_659749, baseEnd_659749] using wordTrace_append hprefix tailTrace_659749
  have hstable : (prefixWord ++ tailWord_659749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659749).length < 2 ^ (prefixWord ++ tailWord_659749).sum := by decide
  have hdescent : baseEnd_659749 < baseStart_659749 := by decide
  rcases family_descends (prefixWord ++ tailWord_659749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659881 : List Nat := [1, 2, 1, 1, 1, 1, 3, 7, 4]
def baseStart_659881 : Nat := 118140960795 + 659881 * 2 ^ 59
def prefixEnd_659881 : Nat := 4983230072969 + 3 ^ 40 * 659881 * 2
def baseEnd_659881 : Nat := 150593834564283531667897

theorem tailTrace_659881 : CollatzResearch.WordTrace tailWord_659881 prefixEnd_659881 150593834564283531667897 := by
  unfold tailWord_659881
  simp only [CollatzResearch.WordTrace]
  refine ⟨24067837322371310547507497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16045224881580873698338331 24067837322371310547507497)
  ·
    refine ⟨18050877991778482910630623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24067837322371310547507497 18050877991778482910630623)
    ·
      refine ⟨27076316987667724365945935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18050877991778482910630623 27076316987667724365945935)
      ·
        refine ⟨40614475481501586548918903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27076316987667724365945935 40614475481501586548918903)
        ·
          refine ⟨60921713222252379823378355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40614475481501586548918903 60921713222252379823378355)
          ·
            refine ⟨91382569833378569735067533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60921713222252379823378355 91382569833378569735067533)
            ·
              refine ⟨34268463687516963650650325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91382569833378569735067533 34268463687516963650650325)
              ·
                refine ⟨803167117676178835562117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 34268463687516963650650325 803167117676178835562117)
                ·
                  refine ⟨150593834564283531667897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 803167117676178835562117 150593834564283531667897)
                  ·
                    rfl

theorem cell21_659881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_659881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659881 prefixEnd_659881 := by exact prefixLift 659881
  have htrace : WordTrace (prefixWord ++ tailWord_659881) baseStart_659881 baseEnd_659881 := by
    simpa [prefixWord, tailWord_659881, baseEnd_659881] using wordTrace_append hprefix tailTrace_659881
  have hstable : (prefixWord ++ tailWord_659881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659881).length < 2 ^ (prefixWord ++ tailWord_659881).sum := by decide
  have hdescent : baseEnd_659881 < baseStart_659881 := by decide
  rcases family_descends (prefixWord ++ tailWord_659881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659901 : List Nat := [1, 4, 1, 2, 2, 4, 1, 3, 3]
def baseStart_659901 : Nat := 118140960795 + 659901 * 2 ^ 59
def prefixEnd_659901 : Nat := 4983230072969 + 3 ^ 40 * 659901 * 2
def baseEnd_659901 : Nat := 150598398836767941334523

theorem tailTrace_659901 : CollatzResearch.WordTrace tailWord_659901 prefixEnd_659901 150598398836767941334523 := by
  unfold tailWord_659901
  simp only [CollatzResearch.WordTrace]
  refine ⟨24068566782298853963235557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16045711188199235975490371 24068566782298853963235557)
  ·
    refine ⟨4512856271681035118106667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24068566782298853963235557 4512856271681035118106667)
    ·
      refine ⟨6769284407521552677160001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4512856271681035118106667 6769284407521552677160001)
      ·
        refine ⟨5076963305641164507870001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6769284407521552677160001 5076963305641164507870001)
        ·
          refine ⟨3807722479230873380902501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5076963305641164507870001 3807722479230873380902501)
          ·
            refine ⟨713947964855788758919219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3807722479230873380902501 713947964855788758919219)
            ·
              refine ⟨1070921947283683138378829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713947964855788758919219 1070921947283683138378829)
              ·
                refine ⟨401595730231381176892061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1070921947283683138378829 401595730231381176892061)
                ·
                  refine ⟨150598398836767941334523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 401595730231381176892061 150598398836767941334523)
                  ·
                    rfl

theorem cell21_659901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_659901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659901 prefixEnd_659901 := by exact prefixLift 659901
  have htrace : WordTrace (prefixWord ++ tailWord_659901) baseStart_659901 baseEnd_659901 := by
    simpa [prefixWord, tailWord_659901, baseEnd_659901] using wordTrace_append hprefix tailTrace_659901
  have hstable : (prefixWord ++ tailWord_659901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659901).length < 2 ^ (prefixWord ++ tailWord_659901).sum := by decide
  have hdescent : baseEnd_659901 < baseStart_659901 := by decide
  rcases family_descends (prefixWord ++ tailWord_659901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659912 : List Nat := [2, 1, 3, 1, 3, 4, 7]
def baseStart_659912 : Nat := 118140960795 + 659912 * 2 ^ 59
def prefixEnd_659912 : Nat := 4983230072969 + 3 ^ 40 * 659912 * 2
def baseEnd_659912 : Nat := 16733434354070485183463

theorem tailTrace_659912 : CollatzResearch.WordTrace tailWord_659912 prefixEnd_659912 16733434354070485183463 := by
  unfold tailWord_659912
  simp only [CollatzResearch.WordTrace]
  refine ⟨12034483992629501420942995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16045978656839335227923993 12034483992629501420942995)
  ·
    refine ⟨18051725988944252131414493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12034483992629501420942995 18051725988944252131414493)
    ·
      refine ⟨6769397245854094549280435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18051725988944252131414493 6769397245854094549280435)
      ·
        refine ⟨10154095868781141823920653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6769397245854094549280435 10154095868781141823920653)
        ·
          refine ⟨3807785950792928183970245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10154095868781141823920653 3807785950792928183970245)
          ·
            refine ⟨713959865773674034494421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3807785950792928183970245 713959865773674034494421)
            ·
              refine ⟨16733434354070485183463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 713959865773674034494421 16733434354070485183463)
              ·
                rfl

theorem cell21_659912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 7].length) (baseStart_659912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_659912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_659912 prefixEnd_659912 := by exact prefixLift 659912
  have htrace : WordTrace (prefixWord ++ tailWord_659912) baseStart_659912 baseEnd_659912 := by
    simpa [prefixWord, tailWord_659912, baseEnd_659912] using wordTrace_append hprefix tailTrace_659912
  have hstable : (prefixWord ++ tailWord_659912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659912).length < 2 ^ (prefixWord ++ tailWord_659912).sum := by decide
  have hdescent : baseEnd_659912 < baseStart_659912 := by decide
  rcases family_descends (prefixWord ++ tailWord_659912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660064 : List Nat := [2, 1, 1, 3, 2, 1, 6, 5]
def baseStart_660064 : Nat := 118140960795 + 660064 * 2 ^ 59
def prefixEnd_660064 : Nat := 4983230072969 + 3 ^ 40 * 660064 * 2
def baseEnd_660064 : Nat := 50211865885838626705841

theorem tailTrace_660064 : CollatzResearch.WordTrace tailWord_660064 prefixEnd_660064 50211865885838626705841 := by
  unfold tailWord_660064
  simp only [CollatzResearch.WordTrace]
  refine ⟨12037255940354166400709623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16049674587138888534279497 12037255940354166400709623)
  ·
    refine ⟨18055883910531249601064435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12037255940354166400709623 18055883910531249601064435)
    ·
      refine ⟨27083825865796874401596653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18055883910531249601064435 27083825865796874401596653)
      ·
        refine ⟨10156434699673827900598745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27083825865796874401596653 10156434699673827900598745)
        ·
          refine ⟨7617326024755370925449059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10156434699673827900598745 7617326024755370925449059)
          ·
            refine ⟨11425989037133056388173589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7617326024755370925449059 11425989037133056388173589)
            ·
              refine ⟨535593236115612018195637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11425989037133056388173589 535593236115612018195637)
              ·
                refine ⟨50211865885838626705841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 535593236115612018195637 50211865885838626705841)
                ·
                  rfl

theorem cell21_660064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 5].length) (baseStart_660064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660064 prefixEnd_660064 := by exact prefixLift 660064
  have htrace : WordTrace (prefixWord ++ tailWord_660064) baseStart_660064 baseEnd_660064 := by
    simpa [prefixWord, tailWord_660064, baseEnd_660064] using wordTrace_append hprefix tailTrace_660064
  have hstable : (prefixWord ++ tailWord_660064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660064).length < 2 ^ (prefixWord ++ tailWord_660064).sum := by decide
  have hdescent : baseEnd_660064 < baseStart_660064 := by decide
  rcases family_descends (prefixWord ++ tailWord_660064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660154 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_660154 : Nat := 118140960795 + 660154 * 2 ^ 59
def prefixEnd_660154 : Nat := 4983230072969 + 3 ^ 40 * 660154 * 2
def baseEnd_660154 : Nat := 150656136883695723617339

theorem tailTrace_660154 : CollatzResearch.WordTrace tailWord_660154 prefixEnd_660154 150656136883695723617339 := by
  unfold tailWord_660154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6019448612595569543048879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16051862966921518781463677 6019448612595569543048879)
  ·
    refine ⟨9029172918893354314573319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6019448612595569543048879 9029172918893354314573319)
    ·
      refine ⟨13543759378340031471859979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9029172918893354314573319 13543759378340031471859979)
      ·
        refine ⟨20315639067510047207789969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13543759378340031471859979 20315639067510047207789969)
        ·
          refine ⟨15236729300632535405842477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20315639067510047207789969 15236729300632535405842477)
          ·
            refine ⟨5713773487737200777190929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15236729300632535405842477 5713773487737200777190929)
            ·
              refine ⟨4285330115802900582893197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5713773487737200777190929 4285330115802900582893197)
              ·
                refine ⟨1606998793426087718584949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4285330115802900582893197 1606998793426087718584949)
                ·
                  refine ⟨150656136883695723617339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1606998793426087718584949 150656136883695723617339)
                  ·
                    rfl

theorem cell21_660154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_660154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660154 prefixEnd_660154 := by exact prefixLift 660154
  have htrace : WordTrace (prefixWord ++ tailWord_660154) baseStart_660154 baseEnd_660154 := by
    simpa [prefixWord, tailWord_660154, baseEnd_660154] using wordTrace_append hprefix tailTrace_660154
  have hstable : (prefixWord ++ tailWord_660154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660154).length < 2 ^ (prefixWord ++ tailWord_660154).sum := by decide
  have hdescent : baseEnd_660154 < baseStart_660154 := by decide
  rcases family_descends (prefixWord ++ tailWord_660154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660261 : List Nat := [1, 3, 1, 2, 3, 1, 2, 4, 4]
def baseStart_660261 : Nat := 118140960795 + 660261 * 2 ^ 59
def prefixEnd_660261 : Nat := 4983230072969 + 3 ^ 40 * 660261 * 2
def baseEnd_660261 : Nat := 150680555741487315333787

theorem tailTrace_660261 : CollatzResearch.WordTrace tailWord_660261 prefixEnd_660261 150680555741487315333787 := by
  unfold tailWord_660261
  simp only [CollatzResearch.WordTrace]
  refine ⟨24081697060994635446340637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16054464707329756964227091 24081697060994635446340637)
  ·
    refine ⟨9030636397872988292377739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24081697060994635446340637 9030636397872988292377739)
    ·
      refine ⟨13545954596809482438566609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9030636397872988292377739 13545954596809482438566609)
      ·
        refine ⟨10159465947607111828924957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13545954596809482438566609 10159465947607111828924957)
        ·
          refine ⟨3809799730352666935846859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10159465947607111828924957 3809799730352666935846859)
          ·
            refine ⟨5714699595529000403770289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809799730352666935846859 5714699595529000403770289)
            ·
              refine ⟨4286024696646750302827717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5714699595529000403770289 4286024696646750302827717)
              ·
                refine ⟨803629630621265681780197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4286024696646750302827717 803629630621265681780197)
                ·
                  refine ⟨150680555741487315333787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 803629630621265681780197 150680555741487315333787)
                  ·
                    rfl

theorem cell21_660261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_660261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660261 prefixEnd_660261 := by exact prefixLift 660261
  have htrace : WordTrace (prefixWord ++ tailWord_660261) baseStart_660261 baseEnd_660261 := by
    simpa [prefixWord, tailWord_660261, baseEnd_660261] using wordTrace_append hprefix tailTrace_660261
  have hstable : (prefixWord ++ tailWord_660261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660261).length < 2 ^ (prefixWord ++ tailWord_660261).sum := by decide
  have hdescent : baseEnd_660261 < baseStart_660261 := by decide
  rcases family_descends (prefixWord ++ tailWord_660261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660275 : List Nat := [1, 1, 1, 2, 6, 1, 1, 8]
def baseStart_660275 : Nat := 118140960795 + 660275 * 2 ^ 59
def prefixEnd_660275 : Nat := 4983230072969 + 3 ^ 40 * 660275 * 2
def baseEnd_660275 : Nat := 50227916910742134033475

theorem tailTrace_660275 : CollatzResearch.WordTrace tailWord_660275 prefixEnd_660275 50227916910742134033475 := by
  unfold tailWord_660275
  simp only [CollatzResearch.WordTrace]
  refine ⟨24082207682943915837350279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16054805121962610558233519 24082207682943915837350279)
  ·
    refine ⟨36123311524415873756025419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24082207682943915837350279 36123311524415873756025419)
    ·
      refine ⟨54184967286623810634038129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36123311524415873756025419 54184967286623810634038129)
      ·
        refine ⟨40638725464967857975528597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54184967286623810634038129 40638725464967857975528597)
        ·
          refine ⟨1904940256170368342602903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40638725464967857975528597 1904940256170368342602903)
          ·
            refine ⟨2857410384255552513904355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904940256170368342602903 2857410384255552513904355)
            ·
              refine ⟨4286115576383328770856533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857410384255552513904355 4286115576383328770856533)
              ·
                refine ⟨50227916910742134033475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4286115576383328770856533 50227916910742134033475)
                ·
                  rfl

theorem cell21_660275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 8].length) (baseStart_660275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660275 prefixEnd_660275 := by exact prefixLift 660275
  have htrace : WordTrace (prefixWord ++ tailWord_660275) baseStart_660275 baseEnd_660275 := by
    simpa [prefixWord, tailWord_660275, baseEnd_660275] using wordTrace_append hprefix tailTrace_660275
  have hstable : (prefixWord ++ tailWord_660275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660275).length < 2 ^ (prefixWord ++ tailWord_660275).sum := by decide
  have hdescent : baseEnd_660275 < baseStart_660275 := by decide
  rcases family_descends (prefixWord ++ tailWord_660275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660337 : List Nat := [1, 2, 2, 2, 1, 4, 2, 3, 4]
def baseStart_660337 : Nat := 118140960795 + 660337 * 2 ^ 59
def prefixEnd_660337 : Nat := 4983230072969 + 3 ^ 40 * 660337 * 2
def baseEnd_660337 : Nat := 150697899976928072066965

theorem tailTrace_660337 : CollatzResearch.WordTrace tailWord_660337 prefixEnd_660337 150697899976928072066965 := by
  unfold tailWord_660337
  simp only [CollatzResearch.WordTrace]
  refine ⟨24084469008719300426107265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16056312672479533617404843 24084469008719300426107265)
  ·
    refine ⟨18063351756539475319580449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24084469008719300426107265 18063351756539475319580449)
    ·
      refine ⟨13547513817404606489685337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18063351756539475319580449 13547513817404606489685337)
      ·
        refine ⟨10160635363053454867264003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13547513817404606489685337 10160635363053454867264003)
        ·
          refine ⟨15240953044580182300896005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10160635363053454867264003 15240953044580182300896005)
          ·
            refine ⟨2857678695858784181418001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15240953044580182300896005 2857678695858784181418001)
            ·
              refine ⟨2143259021894088136063501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2857678695858784181418001 2143259021894088136063501)
              ·
                refine ⟨803722133210283051023813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2143259021894088136063501 803722133210283051023813)
                ·
                  refine ⟨150697899976928072066965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 803722133210283051023813 150697899976928072066965)
                  ·
                    rfl

theorem cell21_660337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_660337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660337 prefixEnd_660337 := by exact prefixLift 660337
  have htrace : WordTrace (prefixWord ++ tailWord_660337) baseStart_660337 baseEnd_660337 := by
    simpa [prefixWord, tailWord_660337, baseEnd_660337] using wordTrace_append hprefix tailTrace_660337
  have hstable : (prefixWord ++ tailWord_660337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660337).length < 2 ^ (prefixWord ++ tailWord_660337).sum := by decide
  have hdescent : baseEnd_660337 < baseStart_660337 := by decide
  rcases family_descends (prefixWord ++ tailWord_660337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660374 : List Nat := [5, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_660374 : Nat := 118140960795 + 660374 * 2 ^ 59
def prefixEnd_660374 : Nat := 4983230072969 + 3 ^ 40 * 660374 * 2
def baseEnd_660374 : Nat := 150706343881024229950223

theorem tailTrace_660374 : CollatzResearch.WordTrace tailWord_660374 prefixEnd_660374 150706343881024229950223 := by
  unfold tailWord_660374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1505363656849078484075261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16057212339723503830136117 1505363656849078484075261)
  ·
    refine ⟨564511371318404431528223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1505363656849078484075261 564511371318404431528223)
    ·
      refine ⟨846767056977606647292335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 564511371318404431528223 846767056977606647292335)
      ·
        refine ⟨1270150585466409970938503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 846767056977606647292335 1270150585466409970938503)
        ·
          refine ⟨1905225878199614956407755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270150585466409970938503 1905225878199614956407755)
          ·
            refine ⟨2857838817299422434611633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905225878199614956407755 2857838817299422434611633)
            ·
              refine ⟨2143379112974566825958725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2857838817299422434611633 2143379112974566825958725)
              ·
                refine ⟨401883583682731279867261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2143379112974566825958725 401883583682731279867261)
                ·
                  refine ⟨150706343881024229950223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 401883583682731279867261 150706343881024229950223)
                  ·
                    rfl

theorem cell21_660374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_660374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660374 prefixEnd_660374 := by exact prefixLift 660374
  have htrace : WordTrace (prefixWord ++ tailWord_660374) baseStart_660374 baseEnd_660374 := by
    simpa [prefixWord, tailWord_660374, baseEnd_660374] using wordTrace_append hprefix tailTrace_660374
  have hstable : (prefixWord ++ tailWord_660374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660374).length < 2 ^ (prefixWord ++ tailWord_660374).sum := by decide
  have hdescent : baseEnd_660374 < baseStart_660374 := by decide
  rcases family_descends (prefixWord ++ tailWord_660374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660416 : List Nat := [2, 1, 1, 2, 3, 5, 1, 3, 3]
def baseStart_660416 : Nat := 118140960795 + 660416 * 2 ^ 59
def prefixEnd_660416 : Nat := 4983230072969 + 3 ^ 40 * 660416 * 2
def baseEnd_660416 : Nat := 150715928853241490250137

theorem tailTrace_660416 : CollatzResearch.WordTrace tailWord_660416 prefixEnd_660416 150715928853241490250137 := by
  unfold tailWord_660416
  simp only [CollatzResearch.WordTrace]
  refine ⟨12043675187716548459116551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16058233583622064612155401 12043675187716548459116551)
  ·
    refine ⟨18065512781574822688674827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12043675187716548459116551 18065512781574822688674827)
    ·
      refine ⟨27098269172362234033012241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18065512781574822688674827 27098269172362234033012241)
      ·
        refine ⟨20323701879271675524759181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27098269172362234033012241 20323701879271675524759181)
        ·
          refine ⟨7621388204726878321784693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20323701879271675524759181 7621388204726878321784693)
          ·
            refine ⟨714505144193144842667315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7621388204726878321784693 714505144193144842667315)
            ·
              refine ⟨1071757716289717264000973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714505144193144842667315 1071757716289717264000973)
              ·
                refine ⟨401909143608643974000365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1071757716289717264000973 401909143608643974000365)
                ·
                  refine ⟨150715928853241490250137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 401909143608643974000365 150715928853241490250137)
                  ·
                    rfl

theorem cell21_660416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 3].length) (baseStart_660416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660416 prefixEnd_660416 := by exact prefixLift 660416
  have htrace : WordTrace (prefixWord ++ tailWord_660416) baseStart_660416 baseEnd_660416 := by
    simpa [prefixWord, tailWord_660416, baseEnd_660416] using wordTrace_append hprefix tailTrace_660416
  have hstable : (prefixWord ++ tailWord_660416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660416).length < 2 ^ (prefixWord ++ tailWord_660416).sum := by decide
  have hdescent : baseEnd_660416 < baseStart_660416 := by decide
  rcases family_descends (prefixWord ++ tailWord_660416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660427 : List Nat := [1, 1, 1, 1, 3, 7, 7]
def baseStart_660427 : Nat := 118140960795 + 660427 * 2 ^ 59
def prefixEnd_660427 : Nat := 4983230072969 + 3 ^ 40 * 660427 * 2
def baseEnd_660427 : Nat := 16746493244789768396309

theorem tailTrace_660427 : CollatzResearch.WordTrace tailWord_660427 prefixEnd_660427 16746493244789768396309 := by
  unfold tailWord_660427
  simp only [CollatzResearch.WordTrace]
  refine ⟨24087751578393245796883535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16058501052262163864589023 24087751578393245796883535)
  ·
    refine ⟨36131627367589868695325303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24087751578393245796883535 36131627367589868695325303)
    ·
      refine ⟨54197441051384803042987955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36131627367589868695325303 54197441051384803042987955)
      ·
        refine ⟨81296161577077204564481933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54197441051384803042987955 81296161577077204564481933)
        ·
          refine ⟨30486060591403951711680725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81296161577077204564481933 30486060591403951711680725)
          ·
            refine ⟨714517045111030118242517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 30486060591403951711680725 714517045111030118242517)
            ·
              refine ⟨16746493244789768396309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 714517045111030118242517 16746493244789768396309)
              ·
                rfl

theorem cell21_660427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 7].length) (baseStart_660427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660427 prefixEnd_660427 := by exact prefixLift 660427
  have htrace : WordTrace (prefixWord ++ tailWord_660427) baseStart_660427 baseEnd_660427 := by
    simpa [prefixWord, tailWord_660427, baseEnd_660427] using wordTrace_append hprefix tailTrace_660427
  have hstable : (prefixWord ++ tailWord_660427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660427).length < 2 ^ (prefixWord ++ tailWord_660427).sum := by decide
  have hdescent : baseEnd_660427 < baseStart_660427 := by decide
  rcases family_descends (prefixWord ++ tailWord_660427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660447 : List Nat := [1, 1, 2, 3, 5, 2, 2, 1, 4]
def baseStart_660447 : Nat := 118140960795 + 660447 * 2 ^ 59
def prefixEnd_660447 : Nat := 4983230072969 + 3 ^ 40 * 660447 * 2
def baseEnd_660447 : Nat := 150723003475592325233407

theorem tailTrace_660447 : CollatzResearch.WordTrace tailWord_660447 prefixEnd_660447 150723003475592325233407 := by
  unfold tailWord_660447
  simp only [CollatzResearch.WordTrace]
  refine ⟨24088481038320789212611595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16058987358880526141741063 24088481038320789212611595)
  ·
    refine ⟨36132721557481183818917393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24088481038320789212611595 36132721557481183818917393)
    ·
      refine ⟨27099541168110887864188045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36132721557481183818917393 27099541168110887864188045)
      ·
        refine ⟨10162327938041582949070517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27099541168110887864188045 10162327938041582949070517)
        ·
          refine ⟨952718244191398401475361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10162327938041582949070517 952718244191398401475361)
          ·
            refine ⟨714538683143548801106521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952718244191398401475361 714538683143548801106521)
            ·
              refine ⟨535904012357661600829891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714538683143548801106521 535904012357661600829891)
              ·
                refine ⟨803856018536492401244837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535904012357661600829891 803856018536492401244837)
                ·
                  refine ⟨150723003475592325233407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 803856018536492401244837 150723003475592325233407)
                  ·
                    rfl

theorem cell21_660447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 4].length) (baseStart_660447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660447 prefixEnd_660447 := by exact prefixLift 660447
  have htrace : WordTrace (prefixWord ++ tailWord_660447) baseStart_660447 baseEnd_660447 := by
    simpa [prefixWord, tailWord_660447, baseEnd_660447] using wordTrace_append hprefix tailTrace_660447
  have hstable : (prefixWord ++ tailWord_660447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660447).length < 2 ^ (prefixWord ++ tailWord_660447).sum := by decide
  have hdescent : baseEnd_660447 < baseStart_660447 := by decide
  rcases family_descends (prefixWord ++ tailWord_660447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660492 : List Nat := [2, 2, 1, 2, 3, 2, 4, 2, 3]
def baseStart_660492 : Nat := 118140960795 + 660492 * 2 ^ 59
def prefixEnd_660492 : Nat := 4983230072969 + 3 ^ 40 * 660492 * 2
def baseEnd_660492 : Nat := 150733273088682246983315

theorem tailTrace_660492 : CollatzResearch.WordTrace tailWord_660492 prefixEnd_660492 150733273088682246983315 := by
  unfold tailWord_660492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12045061161578880948999865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16060081548771841265333153 12045061161578880948999865)
  ·
    refine ⟨9033795871184160711749899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12045061161578880948999865 9033795871184160711749899)
    ·
      refine ⟨13550693806776241067624849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9033795871184160711749899 13550693806776241067624849)
      ·
        refine ⟨10163020355082180800718637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13550693806776241067624849 10163020355082180800718637)
        ·
          refine ⟨3811132633155817800269489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10163020355082180800718637 3811132633155817800269489)
          ·
            refine ⟨2858349474866863350202117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3811132633155817800269489 2858349474866863350202117)
            ·
              refine ⟨535940526537536878162897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2858349474866863350202117 535940526537536878162897)
              ·
                refine ⟨401955394903152658622173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535940526537536878162897 401955394903152658622173)
                ·
                  refine ⟨150733273088682246983315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 401955394903152658622173 150733273088682246983315)
                  ·
                    rfl

theorem cell21_660492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_660492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660492 prefixEnd_660492 := by exact prefixLift 660492
  have htrace : WordTrace (prefixWord ++ tailWord_660492) baseStart_660492 baseEnd_660492 := by
    simpa [prefixWord, tailWord_660492, baseEnd_660492] using wordTrace_append hprefix tailTrace_660492
  have hstable : (prefixWord ++ tailWord_660492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660492).length < 2 ^ (prefixWord ++ tailWord_660492).sum := by decide
  have hdescent : baseEnd_660492 < baseStart_660492 := by decide
  rcases family_descends (prefixWord ++ tailWord_660492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660551 : List Nat := [1, 1, 4, 1, 3, 2, 2, 4, 3]
def baseStart_660551 : Nat := 118140960795 + 660551 * 2 ^ 59
def prefixEnd_660551 : Nat := 4983230072969 + 3 ^ 40 * 660551 * 2
def baseEnd_660551 : Nat := 150746737692511255499861

theorem tailTrace_660551 : CollatzResearch.WordTrace tailWord_660551 prefixEnd_660551 150746737692511255499861 := by
  unfold tailWord_660551
  simp only [CollatzResearch.WordTrace]
  refine ⟨24092274229944014974397507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16061516153296009982931671 24092274229944014974397507)
  ·
    refine ⟨36138411344916022461596261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24092274229944014974397507 36138411344916022461596261)
    ·
      refine ⟨6775952127171754211549299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36138411344916022461596261 6775952127171754211549299)
      ·
        refine ⟨10163928190757631317323949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6775952127171754211549299 10163928190757631317323949)
        ·
          refine ⟨3811473071534111743996481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10163928190757631317323949 3811473071534111743996481)
          ·
            refine ⟨2858604803650583807997361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3811473071534111743996481 2858604803650583807997361)
            ·
              refine ⟨2143953602737937855998021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2858604803650583807997361 2143953602737937855998021)
              ·
                refine ⟨401991300513363347999629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2143953602737937855998021 401991300513363347999629)
                ·
                  refine ⟨150746737692511255499861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 401991300513363347999629 150746737692511255499861)
                  ·
                    rfl

theorem cell21_660551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 3].length) (baseStart_660551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660551 prefixEnd_660551 := by exact prefixLift 660551
  have htrace : WordTrace (prefixWord ++ tailWord_660551) baseStart_660551 baseEnd_660551 := by
    simpa [prefixWord, tailWord_660551, baseEnd_660551] using wordTrace_append hprefix tailTrace_660551
  have hstable : (prefixWord ++ tailWord_660551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660551).length < 2 ^ (prefixWord ++ tailWord_660551).sum := by decide
  have hdescent : baseEnd_660551 < baseStart_660551 := by decide
  rcases family_descends (prefixWord ++ tailWord_660551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660616 : List Nat := [2, 1, 3, 4, 3, 1, 2, 1, 4]
def baseStart_660616 : Nat := 118140960795 + 660616 * 2 ^ 59
def prefixEnd_660616 : Nat := 4983230072969 + 3 ^ 40 * 660616 * 2
def baseEnd_660616 : Nat := 150761571578085586916395

theorem tailTrace_660616 : CollatzResearch.WordTrace tailWord_660616 prefixEnd_660616 150761571578085586916395 := by
  unfold tailWord_660616
  simp only [CollatzResearch.WordTrace]
  refine ⟨12047322487354265537756851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16063096649805687383675801 12047322487354265537756851)
  ·
    refine ⟨18070983731031398306635277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12047322487354265537756851 18070983731031398306635277)
    ·
      refine ⟨6776618899136774364988229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18070983731031398306635277 6776618899136774364988229)
      ·
        refine ⟨1270616043588145193435293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6776618899136774364988229 1270616043588145193435293)
        ·
          refine ⟨476481016345554447538235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1270616043588145193435293 476481016345554447538235)
          ·
            refine ⟨714721524518331671307353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476481016345554447538235 714721524518331671307353)
            ·
              refine ⟨536041143388748753480515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714721524518331671307353 536041143388748753480515)
              ·
                refine ⟨804061715083123130220773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536041143388748753480515 804061715083123130220773)
                ·
                  refine ⟨150761571578085586916395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 804061715083123130220773 150761571578085586916395)
                  ·
                    rfl

theorem cell21_660616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 4].length) (baseStart_660616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660616 prefixEnd_660616 := by exact prefixLift 660616
  have htrace : WordTrace (prefixWord ++ tailWord_660616) baseStart_660616 baseEnd_660616 := by
    simpa [prefixWord, tailWord_660616, baseEnd_660616] using wordTrace_append hprefix tailTrace_660616
  have hstable : (prefixWord ++ tailWord_660616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660616).length < 2 ^ (prefixWord ++ tailWord_660616).sum := by decide
  have hdescent : baseEnd_660616 < baseStart_660616 := by decide
  rcases family_descends (prefixWord ++ tailWord_660616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660672 : List Nat := [2, 1, 1, 2, 6, 2, 1, 6]
def baseStart_660672 : Nat := 118140960795 + 660672 * 2 ^ 59
def prefixEnd_660672 : Nat := 4983230072969 + 3 ^ 40 * 660672 * 2
def baseEnd_660672 : Nat := 50258117180347311327649

theorem tailTrace_660672 : CollatzResearch.WordTrace tailWord_660672 prefixEnd_660672 50258117180347311327649 := by
  unfold tailWord_660672
  simp only [CollatzResearch.WordTrace]
  refine ⟨12048343731252826319776135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16064458308337101759701513 12048343731252826319776135)
  ·
    refine ⟨18072515596879239479664203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12048343731252826319776135 18072515596879239479664203)
    ·
      refine ⟨27108773395318859219496305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18072515596879239479664203 27108773395318859219496305)
      ·
        refine ⟨20331580046489144414622229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27108773395318859219496305 20331580046489144414622229)
        ·
          refine ⟨953042814679178644435417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20331580046489144414622229 953042814679178644435417)
          ·
            refine ⟨714782111009383983326563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 953042814679178644435417 714782111009383983326563)
            ·
              refine ⟨1072173166514075974989845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714782111009383983326563 1072173166514075974989845)
              ·
                refine ⟨50258117180347311327649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1072173166514075974989845 50258117180347311327649)
                ·
                  rfl

theorem cell21_660672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 6].length) (baseStart_660672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660672 prefixEnd_660672 := by exact prefixLift 660672
  have htrace : WordTrace (prefixWord ++ tailWord_660672) baseStart_660672 baseEnd_660672 := by
    simpa [prefixWord, tailWord_660672, baseEnd_660672] using wordTrace_append hprefix tailTrace_660672
  have hstable : (prefixWord ++ tailWord_660672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660672).length < 2 ^ (prefixWord ++ tailWord_660672).sum := by decide
  have hdescent : baseEnd_660672 < baseStart_660672 := by decide
  rcases family_descends (prefixWord ++ tailWord_660672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660717 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 6]
def baseStart_660717 : Nat := 118140960795 + 660717 * 2 ^ 59
def prefixEnd_660717 : Nat := 4983230072969 + 3 ^ 40 * 660717 * 2
def baseEnd_660717 : Nat := 150784621154131855732855

theorem tailTrace_660717 : CollatzResearch.WordTrace tailWord_660717 prefixEnd_660717 150784621154131855732855 := by
  unfold tailWord_660717
  simp only [CollatzResearch.WordTrace]
  refine ⟨24098328747342625324940405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16065552498228416883293603 24098328747342625324940405)
  ·
    refine ⟨2259218320063371124213163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24098328747342625324940405 2259218320063371124213163)
    ·
      refine ⟨3388827480095056686319745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2259218320063371124213163 3388827480095056686319745)
      ·
        refine ⟨2541620610071292514739809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3388827480095056686319745 2541620610071292514739809)
        ·
          refine ⟨1906215457553469386054857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2541620610071292514739809 1906215457553469386054857)
          ·
            refine ⟨1429661593165102039541143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1906215457553469386054857 1429661593165102039541143)
            ·
              refine ⟨2144492389747653059311715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429661593165102039541143 2144492389747653059311715)
              ·
                refine ⟨3216738584621479588967573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144492389747653059311715 3216738584621479588967573)
                ·
                  refine ⟨150784621154131855732855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3216738584621479588967573 150784621154131855732855)
                  ·
                    rfl

theorem cell21_660717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_660717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660717 prefixEnd_660717 := by exact prefixLift 660717
  have htrace : WordTrace (prefixWord ++ tailWord_660717) baseStart_660717 baseEnd_660717 := by
    simpa [prefixWord, tailWord_660717, baseEnd_660717] using wordTrace_append hprefix tailTrace_660717
  have hstable : (prefixWord ++ tailWord_660717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660717).length < 2 ^ (prefixWord ++ tailWord_660717).sum := by decide
  have hdescent : baseEnd_660717 < baseStart_660717 := by decide
  rcases family_descends (prefixWord ++ tailWord_660717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660745 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 5]
def baseStart_660745 : Nat := 118140960795 + 660745 * 2 ^ 59
def prefixEnd_660745 : Nat := 4983230072969 + 3 ^ 40 * 660745 * 2
def baseEnd_660745 : Nat := 150791011135610029266131

theorem tailTrace_660745 : CollatzResearch.WordTrace tailWord_660745 prefixEnd_660745 150791011135610029266131 := by
  unfold tailWord_660745
  simp only [CollatzResearch.WordTrace]
  refine ⟨24099349991241186106959689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16066233327494124071306459 24099349991241186106959689)
  ·
    refine ⟨18074512493430889580219767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24099349991241186106959689 18074512493430889580219767)
    ·
      refine ⟨27111768740146334370329651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18074512493430889580219767 27111768740146334370329651)
      ·
        refine ⟨40667653110219501555494477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27111768740146334370329651 40667653110219501555494477)
        ·
          refine ⟨15250369916332313083310429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40667653110219501555494477 15250369916332313083310429)
          ·
            refine ⟨5718888718624617406241411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15250369916332313083310429 5718888718624617406241411)
            ·
              refine ⟨8578333077936926109362117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5718888718624617406241411 8578333077936926109362117)
              ·
                refine ⟨1608437452113173645505397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8578333077936926109362117 1608437452113173645505397)
                ·
                  refine ⟨150791011135610029266131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1608437452113173645505397 150791011135610029266131)
                  ·
                    rfl

theorem cell21_660745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_660745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660745 prefixEnd_660745 := by exact prefixLift 660745
  have htrace : WordTrace (prefixWord ++ tailWord_660745) baseStart_660745 baseEnd_660745 := by
    simpa [prefixWord, tailWord_660745, baseEnd_660745] using wordTrace_append hprefix tailTrace_660745
  have hstable : (prefixWord ++ tailWord_660745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660745).length < 2 ^ (prefixWord ++ tailWord_660745).sum := by decide
  have hdescent : baseEnd_660745 < baseStart_660745 := by decide
  rcases family_descends (prefixWord ++ tailWord_660745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660748 : List Nat := [2, 2, 1, 2, 2, 5, 2, 5]
def baseStart_660748 : Nat := 118140960795 + 660748 * 2 ^ 59
def prefixEnd_660748 : Nat := 4983230072969 + 3 ^ 40 * 660748 * 2
def baseEnd_660748 : Nat := 50263898592160896905375

theorem tailTrace_660748 : CollatzResearch.WordTrace tailWord_660748 prefixEnd_660748 50263898592160896905375 := by
  unfold tailWord_660748
  simp only [CollatzResearch.WordTrace]
  refine ⟨12049729705115158809659449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16066306273486878412879265 12049729705115158809659449)
  ·
    refine ⟨9037297278836369107244587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12049729705115158809659449 9037297278836369107244587)
    ·
      refine ⟨13555945918254553660866881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9037297278836369107244587 13555945918254553660866881)
      ·
        refine ⟨10166959438690915245650161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13555945918254553660866881 10166959438690915245650161)
        ·
          refine ⟨7625219579018186434237621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10166959438690915245650161 7625219579018186434237621)
          ·
            refine ⟨714864335532954978209777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7625219579018186434237621 714864335532954978209777)
            ·
              refine ⟨536148251649716233657333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714864335532954978209777 536148251649716233657333)
              ·
                refine ⟨50263898592160896905375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 536148251649716233657333 50263898592160896905375)
                ·
                  rfl

theorem cell21_660748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 5].length) (baseStart_660748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660748 prefixEnd_660748 := by exact prefixLift 660748
  have htrace : WordTrace (prefixWord ++ tailWord_660748) baseStart_660748 baseEnd_660748 := by
    simpa [prefixWord, tailWord_660748, baseEnd_660748] using wordTrace_append hprefix tailTrace_660748
  have hstable : (prefixWord ++ tailWord_660748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660748).length < 2 ^ (prefixWord ++ tailWord_660748).sum := by decide
  have hdescent : baseEnd_660748 < baseStart_660748 := by decide
  rcases family_descends (prefixWord ++ tailWord_660748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660754 : List Nat := [3, 2, 4, 2, 1, 2, 1, 3, 3]
def baseStart_660754 : Nat := 118140960795 + 660754 * 2 ^ 59
def prefixEnd_660754 : Nat := 4983230072969 + 3 ^ 40 * 660754 * 2
def baseEnd_660754 : Nat := 150793065058228013616113

theorem tailTrace_660754 : CollatzResearch.WordTrace tailWord_660754 prefixEnd_660754 150793065058228013616113 := by
  unfold tailWord_660754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6024919562052145161009329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16066452165472387096024877 6024919562052145161009329)
  ·
    refine ⟨4518689671539108870756997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6024919562052145161009329 4518689671539108870756997)
    ·
      refine ⟨847254313413582913266937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4518689671539108870756997 847254313413582913266937)
      ·
        refine ⟨635440735060187184950203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 847254313413582913266937 635440735060187184950203)
        ·
          refine ⟨953161102590280777425305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635440735060187184950203 953161102590280777425305)
          ·
            refine ⟨714870826942710583068979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 953161102590280777425305 714870826942710583068979)
            ·
              refine ⟨1072306240414065874603469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714870826942710583068979 1072306240414065874603469)
              ·
                refine ⟨402114840155274702976301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1072306240414065874603469 402114840155274702976301)
                ·
                  refine ⟨150793065058228013616113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402114840155274702976301 150793065058228013616113)
                  ·
                    rfl

theorem cell21_660754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_660754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660754 prefixEnd_660754 := by exact prefixLift 660754
  have htrace : WordTrace (prefixWord ++ tailWord_660754) baseStart_660754 baseEnd_660754 := by
    simpa [prefixWord, tailWord_660754, baseEnd_660754] using wordTrace_append hprefix tailTrace_660754
  have hstable : (prefixWord ++ tailWord_660754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660754).length < 2 ^ (prefixWord ++ tailWord_660754).sum := by decide
  have hdescent : baseEnd_660754 < baseStart_660754 := by decide
  rcases family_descends (prefixWord ++ tailWord_660754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660942 : List Nat := [4, 1, 1, 1, 2, 1, 11]
def baseStart_660942 : Nat := 118140960795 + 660942 * 2 ^ 59
def prefixEnd_660942 : Nat := 4983230072969 + 3 ^ 40 * 660942 * 2
def baseEnd_660942 : Nat := 16759552135509051609155

theorem tailTrace_660942 : CollatzResearch.WordTrace tailWord_660942 prefixEnd_660942 16759552135509051609155 := by
  unfold tailWord_660942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3013316896440936093985135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16071023447684992501254053 3013316896440936093985135)
  ·
    refine ⟨4519975344661404140977703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3013316896440936093985135 4519975344661404140977703)
    ·
      refine ⟨6779963016992106211466555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4519975344661404140977703 6779963016992106211466555)
      ·
        refine ⟨10169944525488159317199833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6779963016992106211466555 10169944525488159317199833)
        ·
          refine ⟨7627458394116119487899875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10169944525488159317199833 7627458394116119487899875)
          ·
            refine ⟨11441187591174179231849813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7627458394116119487899875 11441187591174179231849813)
            ·
              refine ⟨16759552135509051609155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11441187591174179231849813 16759552135509051609155)
              ·
                rfl

theorem cell21_660942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 11].length) (baseStart_660942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660942 prefixEnd_660942 := by exact prefixLift 660942
  have htrace : WordTrace (prefixWord ++ tailWord_660942) baseStart_660942 baseEnd_660942 := by
    simpa [prefixWord, tailWord_660942, baseEnd_660942] using wordTrace_append hprefix tailTrace_660942
  have hstable : (prefixWord ++ tailWord_660942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660942).length < 2 ^ (prefixWord ++ tailWord_660942).sum := by decide
  have hdescent : baseEnd_660942 < baseStart_660942 := by decide
  rcases family_descends (prefixWord ++ tailWord_660942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660948 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 5]
def baseStart_660948 : Nat := 118140960795 + 660948 * 2 ^ 59
def prefixEnd_660948 : Nat := 4983230072969 + 3 ^ 40 * 660948 * 2
def baseEnd_660948 : Nat := 150837338501326787382383

theorem tailTrace_660948 : CollatzResearch.WordTrace tailWord_660948 prefixEnd_660948 150837338501326787382383 := by
  unfold tailWord_660948
  simp only [CollatzResearch.WordTrace]
  refine ⟨12053377004752875888299749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16071169339670501184399665 12053377004752875888299749)
  ·
    refine ⟨2260008188391164229056203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12053377004752875888299749 2260008188391164229056203)
    ·
      refine ⟨3390012282586746343584305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2260008188391164229056203 3390012282586746343584305)
      ·
        refine ⟨2542509211940059757688229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3390012282586746343584305 2542509211940059757688229)
        ·
          refine ⟨476720477238761204566543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2542509211940059757688229 476720477238761204566543)
          ·
            refine ⟨715080715858141806849815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476720477238761204566543 715080715858141806849815)
            ·
              refine ⟨1072621073787212710274723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715080715858141806849815 1072621073787212710274723)
              ·
                refine ⟨1608931610680819065412085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072621073787212710274723 1608931610680819065412085)
                ·
                  refine ⟨150837338501326787382383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1608931610680819065412085 150837338501326787382383)
                  ·
                    rfl

theorem cell21_660948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_660948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_660948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_660948 prefixEnd_660948 := by exact prefixLift 660948
  have htrace : WordTrace (prefixWord ++ tailWord_660948) baseStart_660948 baseEnd_660948 := by
    simpa [prefixWord, tailWord_660948, baseEnd_660948] using wordTrace_append hprefix tailTrace_660948
  have hstable : (prefixWord ++ tailWord_660948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660948).length < 2 ^ (prefixWord ++ tailWord_660948).sum := by decide
  have hdescent : baseEnd_660948 < baseStart_660948 := by decide
  rcases family_descends (prefixWord ++ tailWord_660948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661066 : List Nat := [3, 1, 2, 1, 1, 3, 1, 6, 3]
def baseStart_661066 : Nat := 118140960795 + 661066 * 2 ^ 59
def prefixEnd_661066 : Nat := 4983230072969 + 3 ^ 40 * 661066 * 2
def baseEnd_661066 : Nat := 150864267708984804415475

theorem tailTrace_661066 : CollatzResearch.WordTrace tailWord_661066 prefixEnd_661066 150864267708984804415475 := by
  unfold tailWord_661066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6027764455769564482348763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16074038548718838619596701 6027764455769564482348763)
  ·
    refine ⟨9041646683654346723523145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6027764455769564482348763 9041646683654346723523145)
    ·
      refine ⟨6781235012740760042642359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9041646683654346723523145 6781235012740760042642359)
      ·
        refine ⟨10171852519111140063963539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6781235012740760042642359 10171852519111140063963539)
        ·
          refine ⟨15257778778666710095945309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10171852519111140063963539 15257778778666710095945309)
          ·
            refine ⟨5721667042000016285979491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15257778778666710095945309 5721667042000016285979491)
            ·
              refine ⟨8582500563000024428969237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5721667042000016285979491 8582500563000024428969237)
              ·
                refine ⟨402304713890626145107933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8582500563000024428969237 402304713890626145107933)
                ·
                  refine ⟨150864267708984804415475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402304713890626145107933 150864267708984804415475)
                  ·
                    rfl

theorem cell21_661066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_661066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661066 prefixEnd_661066 := by exact prefixLift 661066
  have htrace : WordTrace (prefixWord ++ tailWord_661066) baseStart_661066 baseEnd_661066 := by
    simpa [prefixWord, tailWord_661066, baseEnd_661066] using wordTrace_append hprefix tailTrace_661066
  have hstable : (prefixWord ++ tailWord_661066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661066).length < 2 ^ (prefixWord ++ tailWord_661066).sum := by decide
  have hdescent : baseEnd_661066 < baseStart_661066 := by decide
  rcases family_descends (prefixWord ++ tailWord_661066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661128 : List Nat := [2, 1, 3, 5, 1, 1, 2, 6]
def baseStart_661128 : Nat := 118140960795 + 661128 * 2 ^ 59
def prefixEnd_661128 : Nat := 4983230072969 + 3 ^ 40 * 661128 * 2
def baseEnd_661128 : Nat := 50292805651228824794005

theorem tailTrace_661128 : CollatzResearch.WordTrace tailWord_661128 prefixEnd_661128 50292805651228824794005 := by
  unfold tailWord_661128
  simp only [CollatzResearch.WordTrace]
  refine ⟨12056659574426821259076019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16075546099235761678768025 12056659574426821259076019)
  ·
    refine ⟨18084989361640231888614029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12056659574426821259076019 18084989361640231888614029)
    ·
      refine ⟨6781871010615086958230261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18084989361640231888614029 6781871010615086958230261)
      ·
        refine ⟨635800407245164402334087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6781871010615086958230261 635800407245164402334087)
        ·
          refine ⟨953700610867746603501131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635800407245164402334087 953700610867746603501131)
          ·
            refine ⟨1430550916301619905251697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953700610867746603501131 1430550916301619905251697)
            ·
              refine ⟨1072913187226214928938773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1430550916301619905251697 1072913187226214928938773)
              ·
                refine ⟨50292805651228824794005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1072913187226214928938773 50292805651228824794005)
                ·
                  rfl

theorem cell21_661128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 6].length) (baseStart_661128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661128 prefixEnd_661128 := by exact prefixLift 661128
  have htrace : WordTrace (prefixWord ++ tailWord_661128) baseStart_661128 baseEnd_661128 := by
    simpa [prefixWord, tailWord_661128, baseEnd_661128] using wordTrace_append hprefix tailTrace_661128
  have hstable : (prefixWord ++ tailWord_661128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661128).length < 2 ^ (prefixWord ++ tailWord_661128).sum := by decide
  have hdescent : baseEnd_661128 < baseStart_661128 := by decide
  rcases family_descends (prefixWord ++ tailWord_661128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661201 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 5]
def baseStart_661201 : Nat := 118140960795 + 661201 * 2 ^ 59
def prefixEnd_661201 : Nat := 4983230072969 + 3 ^ 40 * 661201 * 2
def baseEnd_661201 : Nat := 150895076548254569665199

theorem tailTrace_661201 : CollatzResearch.WordTrace tailWord_661201 prefixEnd_661201 150895076548254569665199 := by
  unfold tailWord_661201
  simp only [CollatzResearch.WordTrace]
  refine ⟨24115981677589175985559457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16077321118392783990372971 24115981677589175985559457)
  ·
    refine ⟨18086986258191881989169593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24115981677589175985559457 18086986258191881989169593)
    ·
      refine ⟨13565239693643911491877195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18086986258191881989169593 13565239693643911491877195)
      ·
        refine ⟨20347859540465867237815793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13565239693643911491877195 20347859540465867237815793)
        ·
          refine ⟨15260894655349400428361845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20347859540465867237815793 15260894655349400428361845)
          ·
            refine ⟨1430708873939006290158923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15260894655349400428361845 1430708873939006290158923)
            ·
              refine ⟨2146063310908509435238385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430708873939006290158923 2146063310908509435238385)
              ·
                refine ⟨1609547483181382076428789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2146063310908509435238385 1609547483181382076428789)
                ·
                  refine ⟨150895076548254569665199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1609547483181382076428789 150895076548254569665199)
                  ·
                    rfl

theorem cell21_661201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_661201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661201 prefixEnd_661201 := by exact prefixLift 661201
  have htrace : WordTrace (prefixWord ++ tailWord_661201) baseStart_661201 baseEnd_661201 := by
    simpa [prefixWord, tailWord_661201, baseEnd_661201] using wordTrace_append hprefix tailTrace_661201
  have hstable : (prefixWord ++ tailWord_661201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661201).length < 2 ^ (prefixWord ++ tailWord_661201).sum := by decide
  have hdescent : baseEnd_661201 < baseStart_661201 := by decide
  rcases family_descends (prefixWord ++ tailWord_661201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661204 : List Nat := [2, 4, 1, 3, 1, 2, 3, 5]
def baseStart_661204 : Nat := 118140960795 + 661204 * 2 ^ 59
def prefixEnd_661204 : Nat := 4983230072969 + 3 ^ 40 * 661204 * 2
def baseEnd_661204 : Nat := 50298587063042410371731

theorem tailTrace_661204 : CollatzResearch.WordTrace tailWord_661204 prefixEnd_661204 50298587063042410371731 := by
  unfold tailWord_661204
  simp only [CollatzResearch.WordTrace]
  refine ⟨12058045548289153748959333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16077394064385538331945777 12058045548289153748959333)
  ·
    refine ⟨2260883540304216327929875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12058045548289153748959333 2260883540304216327929875)
    ·
      refine ⟨3391325310456324491894813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2260883540304216327929875 3391325310456324491894813)
      ·
        refine ⟨1271746991421121684460555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3391325310456324491894813 1271746991421121684460555)
        ·
          refine ⟨1907620487131682526690833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271746991421121684460555 1907620487131682526690833)
          ·
            refine ⟨1430715365348761895018125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1907620487131682526690833 1430715365348761895018125)
            ·
              refine ⟨536518262005785710631797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1430715365348761895018125 536518262005785710631797)
              ·
                refine ⟨50298587063042410371731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 536518262005785710631797 50298587063042410371731)
                ·
                  rfl

theorem cell21_661204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 5].length) (baseStart_661204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661204 prefixEnd_661204 := by exact prefixLift 661204
  have htrace : WordTrace (prefixWord ++ tailWord_661204) baseStart_661204 baseEnd_661204 := by
    simpa [prefixWord, tailWord_661204, baseEnd_661204] using wordTrace_append hprefix tailTrace_661204
  have hstable : (prefixWord ++ tailWord_661204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661204).length < 2 ^ (prefixWord ++ tailWord_661204).sum := by decide
  have hdescent : baseEnd_661204 < baseStart_661204 := by decide
  rcases family_descends (prefixWord ++ tailWord_661204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661215 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 6]
def baseStart_661215 : Nat := 118140960795 + 661215 * 2 ^ 59
def prefixEnd_661215 : Nat := 4983230072969 + 3 ^ 40 * 661215 * 2
def baseEnd_661215 : Nat := 150898271538993656431837

theorem tailTrace_661215 : CollatzResearch.WordTrace tailWord_661215 prefixEnd_661215 150898271538993656431837 := by
  unfold tailWord_661215
  simp only [CollatzResearch.WordTrace]
  refine ⟨24116492299538456376569099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16077661533025637584379399 24116492299538456376569099)
  ·
    refine ⟨36174738449307684564853649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24116492299538456376569099 36174738449307684564853649)
    ·
      refine ⟨27131053836980763423640237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36174738449307684564853649 27131053836980763423640237)
      ·
        refine ⟨10174145188867786283865089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27131053836980763423640237 10174145188867786283865089)
        ·
          refine ⟨7630608891650839712898817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10174145188867786283865089 7630608891650839712898817)
          ·
            refine ⟨5722956668738129784674113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7630608891650839712898817 5722956668738129784674113)
            ·
              refine ⟨4292217501553597338505585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5722956668738129784674113 4292217501553597338505585)
              ·
                refine ⟨3219163126165198003879189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4292217501553597338505585 3219163126165198003879189)
                ·
                  refine ⟨150898271538993656431837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3219163126165198003879189 150898271538993656431837)
                  ·
                    rfl

theorem cell21_661215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_661215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661215 prefixEnd_661215 := by exact prefixLift 661215
  have htrace : WordTrace (prefixWord ++ tailWord_661215) baseStart_661215 baseEnd_661215 := by
    simpa [prefixWord, tailWord_661215, baseEnd_661215] using wordTrace_append hprefix tailTrace_661215
  have hstable : (prefixWord ++ tailWord_661215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661215).length < 2 ^ (prefixWord ++ tailWord_661215).sum := by decide
  have hdescent : baseEnd_661215 < baseStart_661215 := by decide
  rcases family_descends (prefixWord ++ tailWord_661215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661429 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 5]
def baseStart_661429 : Nat := 118140960795 + 661429 * 2 ^ 59
def prefixEnd_661429 : Nat := 4983230072969 + 3 ^ 40 * 661429 * 2
def baseEnd_661429 : Nat := 150947109254576839864733

theorem tailTrace_661429 : CollatzResearch.WordTrace tailWord_661429 prefixEnd_661429 150947109254576839864733 := by
  unfold tailWord_661429
  simp only [CollatzResearch.WordTrace]
  refine ⟨24124297520763170924859341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16082865013842113949906227 24124297520763170924859341)
  ·
    refine ⟨9046611570286189096822253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24124297520763170924859341 9046611570286189096822253)
    ·
      refine ⟨3392479338857320911308345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9046611570286189096822253 3392479338857320911308345)
      ·
        refine ⟨2544359504142990683481259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3392479338857320911308345 2544359504142990683481259)
        ·
          refine ⟨3816539256214486025221889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2544359504142990683481259 3816539256214486025221889)
          ·
            refine ⟨2862404442160864518916417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3816539256214486025221889 2862404442160864518916417)
            ·
              refine ⟨2146803331620648389187313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2862404442160864518916417 2146803331620648389187313)
              ·
                refine ⟨1610102498715486291890485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2146803331620648389187313 1610102498715486291890485)
                ·
                  refine ⟨150947109254576839864733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1610102498715486291890485 150947109254576839864733)
                  ·
                    rfl

theorem cell21_661429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_661429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661429 prefixEnd_661429 := by exact prefixLift 661429
  have htrace : WordTrace (prefixWord ++ tailWord_661429) baseStart_661429 baseEnd_661429 := by
    simpa [prefixWord, tailWord_661429, baseEnd_661429] using wordTrace_append hprefix tailTrace_661429
  have hstable : (prefixWord ++ tailWord_661429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661429).length < 2 ^ (prefixWord ++ tailWord_661429).sum := by decide
  have hdescent : baseEnd_661429 < baseStart_661429 := by decide
  rcases family_descends (prefixWord ++ tailWord_661429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661460 : List Nat := [2, 4, 1, 2, 1, 1, 2, 4, 4]
def baseStart_661460 : Nat := 118140960795 + 661460 * 2 ^ 59
def prefixEnd_661460 : Nat := 4983230072969 + 3 ^ 40 * 661460 * 2
def baseEnd_661460 : Nat := 150954183876927674848003

theorem tailTrace_661460 : CollatzResearch.WordTrace tailWord_661460 prefixEnd_661460 150954183876927674848003 := by
  unfold tailWord_661460
  simp only [CollatzResearch.WordTrace]
  refine ⟨12062714091825431609618917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16083618789100575479491889 12062714091825431609618917)
  ·
    refine ⟨2261758892217268426803547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12062714091825431609618917 2261758892217268426803547)
    ·
      refine ⟨3392638338325902640205321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2261758892217268426803547 3392638338325902640205321)
      ·
        refine ⟨2544478753744426980153991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3392638338325902640205321 2544478753744426980153991)
        ·
          refine ⟨3816718130616640470230987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2544478753744426980153991 3816718130616640470230987)
          ·
            refine ⟨5725077195924960705346481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3816718130616640470230987 5725077195924960705346481)
            ·
              refine ⟨4293807896943720529009861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5725077195924960705346481 4293807896943720529009861)
              ·
                refine ⟨805088980676947599189349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4293807896943720529009861 805088980676947599189349)
                ·
                  refine ⟨150954183876927674848003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805088980676947599189349 150954183876927674848003)
                  ·
                    rfl

theorem cell21_661460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_661460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661460 prefixEnd_661460 := by exact prefixLift 661460
  have htrace : WordTrace (prefixWord ++ tailWord_661460) baseStart_661460 baseEnd_661460 := by
    simpa [prefixWord, tailWord_661460, baseEnd_661460] using wordTrace_append hprefix tailTrace_661460
  have hstable : (prefixWord ++ tailWord_661460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661460).length < 2 ^ (prefixWord ++ tailWord_661460).sum := by decide
  have hdescent : baseEnd_661460 < baseStart_661460 := by decide
  rcases family_descends (prefixWord ++ tailWord_661460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661488 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 5]
def baseStart_661488 : Nat := 118140960795 + 661488 * 2 ^ 59
def prefixEnd_661488 : Nat := 4983230072969 + 3 ^ 40 * 661488 * 2
def baseEnd_661488 : Nat := 150960573858405848381279

theorem tailTrace_661488 : CollatzResearch.WordTrace tailWord_661488 prefixEnd_661488 150960573858405848381279 := by
  unfold tailWord_661488
  simp only [CollatzResearch.WordTrace]
  refine ⟨12063224713774712000628559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16084299618366282667504745 12063224713774712000628559)
  ·
    refine ⟨18094837070662068000942839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12063224713774712000628559 18094837070662068000942839)
    ·
      refine ⟨27142255605993102001414259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18094837070662068000942839 27142255605993102001414259)
      ·
        refine ⟨40713383408989653002121389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27142255605993102001414259 40713383408989653002121389)
        ·
          refine ⟨15267518778371119875795521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40713383408989653002121389 15267518778371119875795521)
          ·
            refine ⟨11450639083778339906846641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15267518778371119875795521 11450639083778339906846641)
            ·
              refine ⟨8587979312833754930134981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11450639083778339906846641 8587979312833754930134981)
              ·
                refine ⟨1610246121156329049400309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8587979312833754930134981 1610246121156329049400309)
                ·
                  refine ⟨150960573858405848381279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1610246121156329049400309 150960573858405848381279)
                  ·
                    rfl

theorem cell21_661488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_661488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661488 prefixEnd_661488 := by exact prefixLift 661488
  have htrace : WordTrace (prefixWord ++ tailWord_661488) baseStart_661488 baseEnd_661488 := by
    simpa [prefixWord, tailWord_661488, baseEnd_661488] using wordTrace_append hprefix tailTrace_661488
  have hstable : (prefixWord ++ tailWord_661488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661488).length < 2 ^ (prefixWord ++ tailWord_661488).sum := by decide
  have hdescent : baseEnd_661488 < baseStart_661488 := by decide
  rcases family_descends (prefixWord ++ tailWord_661488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661556 : List Nat := [2, 5, 1, 2, 2, 1, 2, 3, 3]
def baseStart_661556 : Nat := 118140960795 + 661556 * 2 ^ 59
def prefixEnd_661556 : Nat := 4983230072969 + 3 ^ 40 * 661556 * 2
def baseEnd_661556 : Nat := 150976092384852841247807

theorem tailTrace_661556 : CollatzResearch.WordTrace tailWord_661556 prefixEnd_661556 150976092384852841247807 := by
  unfold tailWord_661556
  simp only [CollatzResearch.WordTrace]
  refine ⟨12064464795651535807366261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16085953060868714409821681 12064464795651535807366261)
  ·
    refine ⟨1131043574592331481940587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12064464795651535807366261 1131043574592331481940587)
    ·
      refine ⟨1696565361888497222910881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1131043574592331481940587 1696565361888497222910881)
      ·
        refine ⟨1272424021416372917183161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1696565361888497222910881 1272424021416372917183161)
        ·
          refine ⟨954318016062279687887371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1272424021416372917183161 954318016062279687887371)
          ·
            refine ⟨1431477024093419531831057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954318016062279687887371 1431477024093419531831057)
            ·
              refine ⟨1073607768070064648873293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1431477024093419531831057 1073607768070064648873293)
              ·
                refine ⟨402602913026274243327485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1073607768070064648873293 402602913026274243327485)
                ·
                  refine ⟨150976092384852841247807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402602913026274243327485 150976092384852841247807)
                  ·
                    rfl

theorem cell21_661556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_661556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661556 prefixEnd_661556 := by exact prefixLift 661556
  have htrace : WordTrace (prefixWord ++ tailWord_661556) baseStart_661556 baseEnd_661556 := by
    simpa [prefixWord, tailWord_661556, baseEnd_661556] using wordTrace_append hprefix tailTrace_661556
  have hstable : (prefixWord ++ tailWord_661556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661556).length < 2 ^ (prefixWord ++ tailWord_661556).sum := by decide
  have hdescent : baseEnd_661556 < baseStart_661556 := by decide
  rcases family_descends (prefixWord ++ tailWord_661556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661564 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 7]
def baseStart_661564 : Nat := 118140960795 + 661564 * 2 ^ 59
def prefixEnd_661564 : Nat := 4983230072969 + 3 ^ 40 * 661564 * 2
def baseEnd_661564 : Nat := 150977918093846605114457

theorem tailTrace_661564 : CollatzResearch.WordTrace tailWord_661564 prefixEnd_661564 150977918093846605114457 := by
  unfold tailWord_661564
  simp only [CollatzResearch.WordTrace]
  refine ⟨12064610687637044490511873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16086147583516059320682497 12064610687637044490511873)
  ·
    refine ⟨9048458015727783367883905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12064610687637044490511873 9048458015727783367883905)
    ·
      refine ⟨6786343511795837525912929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9048458015727783367883905 6786343511795837525912929)
      ·
        refine ⟨5089757633846878144434697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6786343511795837525912929 5089757633846878144434697)
        ·
          refine ⟨3817318225385158608326023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5089757633846878144434697 3817318225385158608326023)
          ·
            refine ⟨5725977338077737912489035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3817318225385158608326023 5725977338077737912489035)
            ·
              refine ⟨8588966007116606868733553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5725977338077737912489035 8588966007116606868733553)
              ·
                refine ⟨6441724505337455151550165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8588966007116606868733553 6441724505337455151550165)
                ·
                  refine ⟨150977918093846605114457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6441724505337455151550165 150977918093846605114457)
                  ·
                    rfl

theorem cell21_661564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_661564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661564 prefixEnd_661564 := by exact prefixLift 661564
  have htrace : WordTrace (prefixWord ++ tailWord_661564) baseStart_661564 baseEnd_661564 := by
    simpa [prefixWord, tailWord_661564, baseEnd_661564] using wordTrace_append hprefix tailTrace_661564
  have hstable : (prefixWord ++ tailWord_661564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661564).length < 2 ^ (prefixWord ++ tailWord_661564).sum := by decide
  have hdescent : baseEnd_661564 < baseStart_661564 := by decide
  rcases family_descends (prefixWord ++ tailWord_661564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661609 : List Nat := [1, 2, 1, 1, 1, 5, 3, 7]
def baseStart_661609 : Nat := 118140960795 + 661609 * 2 ^ 59
def prefixEnd_661609 : Nat := 4983230072969 + 3 ^ 40 * 661609 * 2
def baseEnd_661609 : Nat := 50329395902312175621455

theorem tailTrace_661609 : CollatzResearch.WordTrace tailWord_661609 prefixEnd_661609 50329395902312175621455 := by
  unfold tailWord_661609
  simp only [CollatzResearch.WordTrace]
  refine ⟨24130862660111061666411881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16087241773407374444274587 24130862660111061666411881)
  ·
    refine ⟨18098146995083296249808911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24130862660111061666411881 18098146995083296249808911)
    ·
      refine ⟨27147220492624944374713367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18098146995083296249808911 27147220492624944374713367)
      ·
        refine ⟨40720830738937416562070051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27147220492624944374713367 40720830738937416562070051)
        ·
          refine ⟨61081246108406124843105077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40720830738937416562070051 61081246108406124843105077)
          ·
            refine ⟨5726366822663074204041101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61081246108406124843105077 5726366822663074204041101)
            ·
              refine ⟨2147387558498652826515413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5726366822663074204041101 2147387558498652826515413)
              ·
                refine ⟨50329395902312175621455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2147387558498652826515413 50329395902312175621455)
                ·
                  rfl

theorem cell21_661609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 7].length) (baseStart_661609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661609 prefixEnd_661609 := by exact prefixLift 661609
  have htrace : WordTrace (prefixWord ++ tailWord_661609) baseStart_661609 baseEnd_661609 := by
    simpa [prefixWord, tailWord_661609, baseEnd_661609] using wordTrace_append hprefix tailTrace_661609
  have hstable : (prefixWord ++ tailWord_661609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661609).length < 2 ^ (prefixWord ++ tailWord_661609).sum := by decide
  have hdescent : baseEnd_661609 < baseStart_661609 := by decide
  rcases family_descends (prefixWord ++ tailWord_661609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661646 : List Nat := [4, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_661646 : Nat := 118140960795 + 661646 * 2 ^ 59
def prefixEnd_661646 : Nat := 4983230072969 + 3 ^ 40 * 661646 * 2
def baseEnd_661646 : Nat := 150996631611032684747623

theorem tailTrace_661646 : CollatzResearch.WordTrace tailWord_661646 prefixEnd_661646 150996631611032684747623 := by
  unfold tailWord_661646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016526520122127123188599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16088141440651344657005861 3016526520122127123188599)
  ·
    refine ⟨4524789780183190684782899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3016526520122127123188599 4524789780183190684782899)
    ·
      refine ⟨6787184670274786027174349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4524789780183190684782899 6787184670274786027174349)
      ·
        refine ⟨2545194251353044760190381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6787184670274786027174349 2545194251353044760190381)
        ·
          refine ⟨954447844257391785071393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2545194251353044760190381 954447844257391785071393)
          ·
            refine ⟨715835883193043838803545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954447844257391785071393 715835883193043838803545)
            ·
              refine ⟨536876912394782879102659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715835883193043838803545 536876912394782879102659)
              ·
                refine ⟨805315368592174318653989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536876912394782879102659 805315368592174318653989)
                ·
                  refine ⟨150996631611032684747623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805315368592174318653989 150996631611032684747623)
                  ·
                    rfl

theorem cell21_661646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_661646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661646 prefixEnd_661646 := by exact prefixLift 661646
  have htrace : WordTrace (prefixWord ++ tailWord_661646) baseStart_661646 baseEnd_661646 := by
    simpa [prefixWord, tailWord_661646, baseEnd_661646] using wordTrace_append hprefix tailTrace_661646
  have hstable : (prefixWord ++ tailWord_661646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661646).length < 2 ^ (prefixWord ++ tailWord_661646).sum := by decide
  have hdescent : baseEnd_661646 < baseStart_661646 := by decide
  rcases family_descends (prefixWord ++ tailWord_661646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661750 : List Nat := [5, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_661750 : Nat := 118140960795 + 661750 * 2 ^ 59
def prefixEnd_661750 : Nat := 4983230072969 + 3 ^ 40 * 661750 * 2
def baseEnd_661750 : Nat := 151020365827951615014077

theorem tailTrace_661750 : CollatzResearch.WordTrace tailWord_661750 prefixEnd_661750 151020365827951615014077 := by
  unfold tailWord_661750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1508500334537515171705919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16090670235066828498196469 1508500334537515171705919)
  ·
    refine ⟨2262750501806272757558879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1508500334537515171705919 2262750501806272757558879)
    ·
      refine ⟨3394125752709409136338319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2262750501806272757558879 3394125752709409136338319)
      ·
        refine ⟨5091188629064113704507479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3394125752709409136338319 5091188629064113704507479)
        ·
          refine ⟨7636782943596170556761219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5091188629064113704507479 7636782943596170556761219)
          ·
            refine ⟨11455174415394255835141829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7636782943596170556761219 11455174415394255835141829)
            ·
              refine ⟨2147845202886422969089093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11455174415394255835141829 2147845202886422969089093)
              ·
                refine ⟨402720975541204306704205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2147845202886422969089093 402720975541204306704205)
                ·
                  refine ⟨151020365827951615014077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402720975541204306704205 151020365827951615014077)
                  ·
                    rfl

theorem cell21_661750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_661750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661750 prefixEnd_661750 := by exact prefixLift 661750
  have htrace : WordTrace (prefixWord ++ tailWord_661750) baseStart_661750 baseEnd_661750 := by
    simpa [prefixWord, tailWord_661750, baseEnd_661750] using wordTrace_append hprefix tailTrace_661750
  have hstable : (prefixWord ++ tailWord_661750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661750).length < 2 ^ (prefixWord ++ tailWord_661750).sum := by decide
  have hdescent : baseEnd_661750 < baseStart_661750 := by decide
  rcases family_descends (prefixWord ++ tailWord_661750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661761 : List Nat := [1, 2, 4, 1, 1, 2, 2, 8]
def baseStart_661761 : Nat := 118140960795 + 661761 * 2 ^ 59
def prefixEnd_661761 : Nat := 4983230072969 + 3 ^ 40 * 661761 * 2
def baseEnd_661761 : Nat := 50340958725939346776907

theorem tailTrace_661761 : CollatzResearch.WordTrace tailWord_661761 prefixEnd_661761 50340958725939346776907 := by
  unfold tailWord_661761
  simp only [CollatzResearch.WordTrace]
  refine ⟨24136406555560391625945137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16090937703706927750630091 24136406555560391625945137)
  ·
    refine ⟨18102304916670293719458853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24136406555560391625945137 18102304916670293719458853)
    ·
      refine ⟨3394182171875680072398535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18102304916670293719458853 3394182171875680072398535)
      ·
        refine ⟨5091273257813520108597803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3394182171875680072398535 5091273257813520108597803)
        ·
          refine ⟨7636909886720280162896705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5091273257813520108597803 7636909886720280162896705)
          ·
            refine ⟨5727682415040210122172529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7636909886720280162896705 5727682415040210122172529)
            ·
              refine ⟨4295761811280157591629397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5727682415040210122172529 4295761811280157591629397)
              ·
                refine ⟨50340958725939346776907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4295761811280157591629397 50340958725939346776907)
                ·
                  rfl

theorem cell21_661761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 8].length) (baseStart_661761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661761 prefixEnd_661761 := by exact prefixLift 661761
  have htrace : WordTrace (prefixWord ++ tailWord_661761) baseStart_661761 baseEnd_661761 := by
    simpa [prefixWord, tailWord_661761, baseEnd_661761] using wordTrace_append hprefix tailTrace_661761
  have hstable : (prefixWord ++ tailWord_661761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661761).length < 2 ^ (prefixWord ++ tailWord_661761).sum := by decide
  have hdescent : baseEnd_661761 < baseStart_661761 := by decide
  rcases family_descends (prefixWord ++ tailWord_661761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661823 : List Nat := [1, 1, 2, 2, 4, 1, 3, 3, 4]
def baseStart_661823 : Nat := 118140960795 + 661823 * 2 ^ 59
def prefixEnd_661823 : Nat := 4983230072969 + 3 ^ 40 * 661823 * 2
def baseEnd_661823 : Nat := 151037025422519710297261

theorem tailTrace_661823 : CollatzResearch.WordTrace tailWord_661823 prefixEnd_661823 151037025422519710297261 := by
  unfold tailWord_661823
  simp only [CollatzResearch.WordTrace]
  refine ⟨24138667881335776214702123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16092445254223850809801415 24138667881335776214702123)
  ·
    refine ⟨36208001822003664322053185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24138667881335776214702123 36208001822003664322053185)
    ·
      refine ⟨27156001366502748241539889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36208001822003664322053185 27156001366502748241539889)
      ·
        refine ⟨20367001024877061181154917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27156001366502748241539889 20367001024877061181154917)
        ·
          refine ⟨3818812692164448971466547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20367001024877061181154917 3818812692164448971466547)
          ·
            refine ⟨5728219038246673457199821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818812692164448971466547 5728219038246673457199821)
            ·
              refine ⟨2148082139342502546449933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5728219038246673457199821 2148082139342502546449933)
              ·
                refine ⟨805530802253438454918725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2148082139342502546449933 805530802253438454918725)
                ·
                  refine ⟨151037025422519710297261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805530802253438454918725 151037025422519710297261)
                  ·
                    rfl

theorem cell21_661823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 4].length) (baseStart_661823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661823 prefixEnd_661823 := by exact prefixLift 661823
  have htrace : WordTrace (prefixWord ++ tailWord_661823) baseStart_661823 baseEnd_661823 := by
    simpa [prefixWord, tailWord_661823, baseEnd_661823] using wordTrace_append hprefix tailTrace_661823
  have hstable : (prefixWord ++ tailWord_661823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661823).length < 2 ^ (prefixWord ++ tailWord_661823).sum := by decide
  have hdescent : baseEnd_661823 < baseStart_661823 := by decide
  rcases family_descends (prefixWord ++ tailWord_661823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661902 : List Nat := [4, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_661902 : Nat := 118140960795 + 661902 * 2 ^ 59
def prefixEnd_661902 : Nat := 4983230072969 + 3 ^ 40 * 661902 * 2
def baseEnd_661902 : Nat := 151055054298833128480433

theorem tailTrace_661902 : CollatzResearch.WordTrace tailWord_661902 prefixEnd_661902 151055054298833128480433 := by
  unfold tailWord_661902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3017693656006196588353495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16094366165366381804551973 3017693656006196588353495)
  ·
    refine ⟨4526540484009294882530243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3017693656006196588353495 4526540484009294882530243)
    ·
      refine ⟨6789810726013942323795365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4526540484009294882530243 6789810726013942323795365)
      ·
        refine ⟨1273089511127614185711631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6789810726013942323795365 1273089511127614185711631)
        ·
          refine ⟨1909634266691421278567447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1273089511127614185711631 1909634266691421278567447)
          ·
            refine ⟨2864451400037131917851171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909634266691421278567447 2864451400037131917851171)
            ·
              refine ⟨4296677100055697876776757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2864451400037131917851171 4296677100055697876776757)
              ·
                refine ⟨402813478130221675947821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4296677100055697876776757 402813478130221675947821)
                ·
                  refine ⟨151055054298833128480433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402813478130221675947821 151055054298833128480433)
                  ·
                    rfl

theorem cell21_661902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_661902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661902 prefixEnd_661902 := by exact prefixLift 661902
  have htrace : WordTrace (prefixWord ++ tailWord_661902) baseStart_661902 baseEnd_661902 := by
    simpa [prefixWord, tailWord_661902, baseEnd_661902] using wordTrace_append hprefix tailTrace_661902
  have hstable : (prefixWord ++ tailWord_661902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661902).length < 2 ^ (prefixWord ++ tailWord_661902).sum := by decide
  have hdescent : baseEnd_661902 < baseStart_661902 := by decide
  rcases family_descends (prefixWord ++ tailWord_661902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661953 : List Nat := [1, 2, 7, 1, 1, 2, 1, 3, 3]
def baseStart_661953 : Nat := 118140960795 + 661953 * 2 ^ 59
def prefixEnd_661953 : Nat := 4983230072969 + 3 ^ 40 * 661953 * 2
def baseEnd_661953 : Nat := 151066693193668373130329

theorem tailTrace_661953 : CollatzResearch.WordTrace tailWord_661953 prefixEnd_661953 151066693193668373130329 := by
  unfold tailWord_661953
  simp only [CollatzResearch.WordTrace]
  refine ⟨24143409370864808416934513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16095606247243205611289675 24143409370864808416934513)
  ·
    refine ⟨18107557028148606312700885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24143409370864808416934513 18107557028148606312700885)
    ·
      refine ⟨424395867847232960453927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18107557028148606312700885 424395867847232960453927)
      ·
        refine ⟨636593801770849440680891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424395867847232960453927 636593801770849440680891)
        ·
          refine ⟨954890702656274161021337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636593801770849440680891 954890702656274161021337)
          ·
            refine ⟨716168026992205620766003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954890702656274161021337 716168026992205620766003)
            ·
              refine ⟨1074252040488308431149005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716168026992205620766003 1074252040488308431149005)
              ·
                refine ⟨402844515183115661680877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1074252040488308431149005 402844515183115661680877)
                ·
                  refine ⟨151066693193668373130329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402844515183115661680877 151066693193668373130329)
                  ·
                    rfl

theorem cell21_661953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 3].length) (baseStart_661953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661953 prefixEnd_661953 := by exact prefixLift 661953
  have htrace : WordTrace (prefixWord ++ tailWord_661953) baseStart_661953 baseEnd_661953 := by
    simpa [prefixWord, tailWord_661953, baseEnd_661953] using wordTrace_append hprefix tailTrace_661953
  have hstable : (prefixWord ++ tailWord_661953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661953).length < 2 ^ (prefixWord ++ tailWord_661953).sum := by decide
  have hdescent : baseEnd_661953 < baseStart_661953 := by decide
  rcases family_descends (prefixWord ++ tailWord_661953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661961 : List Nat := [1, 2, 1, 1, 2, 1, 7, 3, 3]
def baseStart_661961 : Nat := 118140960795 + 661961 * 2 ^ 59
def prefixEnd_661961 : Nat := 4983230072969 + 3 ^ 40 * 661961 * 2
def baseEnd_661961 : Nat := 151068518902662136996979

theorem tailTrace_661961 : CollatzResearch.WordTrace tailWord_661961 prefixEnd_661961 151068518902662136996979 := by
  unfold tailWord_661961
  simp only [CollatzResearch.WordTrace]
  refine ⟨24143701154835825783225737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16095800769890550522150491 24143701154835825783225737)
  ·
    refine ⟨18107775866126869337419303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24143701154835825783225737 18107775866126869337419303)
    ·
      refine ⟨27161663799190304006128955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18107775866126869337419303 27161663799190304006128955)
      ·
        refine ⟨40742495698785456009193433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27161663799190304006128955 40742495698785456009193433)
        ·
          refine ⟨30556871774089092006895075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40742495698785456009193433 30556871774089092006895075)
          ·
            refine ⟨45835307661133638010342613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30556871774089092006895075 45835307661133638010342613)
            ·
              refine ⟨1074265023307819640867405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 45835307661133638010342613 1074265023307819640867405)
              ·
                refine ⟨402849383740432365325277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1074265023307819640867405 402849383740432365325277)
                ·
                  refine ⟨151068518902662136996979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402849383740432365325277 151068518902662136996979)
                  ·
                    rfl

theorem cell21_661961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 3].length) (baseStart_661961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661961 prefixEnd_661961 := by exact prefixLift 661961
  have htrace : WordTrace (prefixWord ++ tailWord_661961) baseStart_661961 baseEnd_661961 := by
    simpa [prefixWord, tailWord_661961, baseEnd_661961] using wordTrace_append hprefix tailTrace_661961
  have hstable : (prefixWord ++ tailWord_661961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661961).length < 2 ^ (prefixWord ++ tailWord_661961).sum := by decide
  have hdescent : baseEnd_661961 < baseStart_661961 := by decide
  rcases family_descends (prefixWord ++ tailWord_661961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661978 : List Nat := [3, 1, 1, 2, 3, 1, 5, 2, 3]
def baseStart_661978 : Nat := 118140960795 + 661978 * 2 ^ 59
def prefixEnd_661978 : Nat := 4983230072969 + 3 ^ 40 * 661978 * 2
def baseEnd_661978 : Nat := 151072398534273885213611

theorem tailTrace_661978 : CollatzResearch.WordTrace tailWord_661978 prefixEnd_661978 151072398534273885213611 := by
  unfold tailWord_661978
  simp only [CollatzResearch.WordTrace]
  refine ⟨6036080298943559421648647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16096214130516158457729725 6036080298943559421648647)
  ·
    refine ⟨9054120448415339132472971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6036080298943559421648647 9054120448415339132472971)
    ·
      refine ⟨13581180672623008698709457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9054120448415339132472971 13581180672623008698709457)
      ·
        refine ⟨10185885504467256524032093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13581180672623008698709457 10185885504467256524032093)
        ·
          refine ⟨3819707064175221196512035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10185885504467256524032093 3819707064175221196512035)
          ·
            refine ⟨5729560596262831794768053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3819707064175221196512035 5729560596262831794768053)
            ·
              refine ⟨537146305899640480759505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5729560596262831794768053 537146305899640480759505)
              ·
                refine ⟨402859729424730360569629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537146305899640480759505 402859729424730360569629)
                ·
                  refine ⟨151072398534273885213611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402859729424730360569629 151072398534273885213611)
                  ·
                    rfl

theorem cell21_661978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_661978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661978 prefixEnd_661978 := by exact prefixLift 661978
  have htrace : WordTrace (prefixWord ++ tailWord_661978) baseStart_661978 baseEnd_661978 := by
    simpa [prefixWord, tailWord_661978, baseEnd_661978] using wordTrace_append hprefix tailTrace_661978
  have hstable : (prefixWord ++ tailWord_661978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661978).length < 2 ^ (prefixWord ++ tailWord_661978).sum := by decide
  have hdescent : baseEnd_661978 < baseStart_661978 := by decide
  rcases family_descends (prefixWord ++ tailWord_661978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661992 : List Nat := [2, 1, 4, 1, 1, 3, 4, 1, 4]
def baseStart_661992 : Nat := 118140960795 + 661992 * 2 ^ 59
def prefixEnd_661992 : Nat := 4983230072969 + 3 ^ 40 * 661992 * 2
def baseEnd_661992 : Nat := 151075593525012971980249

theorem tailTrace_661992 : CollatzResearch.WordTrace tailWord_661992 prefixEnd_661992 151075593525012971980249 := by
  unfold tailWord_661992
  simp only [CollatzResearch.WordTrace]
  refine ⟨12072415908861759038802115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16096554545149012051736153 12072415908861759038802115)
  ·
    refine ⟨18108623863292638558203173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12072415908861759038802115 18108623863292638558203173)
    ·
      refine ⟨3395366974367369729663095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18108623863292638558203173 3395366974367369729663095)
      ·
        refine ⟨5093050461551054594494643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3395366974367369729663095 5093050461551054594494643)
        ·
          refine ⟨7639575692326581891741965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5093050461551054594494643 7639575692326581891741965)
          ·
            refine ⟨2864840884622468209403237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7639575692326581891741965 2864840884622468209403237)
            ·
              refine ⟨537157665866712789263107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2864840884622468209403237 537157665866712789263107)
              ·
                refine ⟨805736498800069183894661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537157665866712789263107 805736498800069183894661)
                ·
                  refine ⟨151075593525012971980249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805736498800069183894661 151075593525012971980249)
                  ·
                    rfl

theorem cell21_661992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_661992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_661992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_661992 prefixEnd_661992 := by exact prefixLift 661992
  have htrace : WordTrace (prefixWord ++ tailWord_661992) baseStart_661992 baseEnd_661992 := by
    simpa [prefixWord, tailWord_661992, baseEnd_661992] using wordTrace_append hprefix tailTrace_661992
  have hstable : (prefixWord ++ tailWord_661992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661992).length < 2 ^ (prefixWord ++ tailWord_661992).sum := by decide
  have hdescent : baseEnd_661992 < baseStart_661992 := by decide
  rcases family_descends (prefixWord ++ tailWord_661992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662003 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 7]
def baseStart_662003 : Nat := 118140960795 + 662003 * 2 ^ 59
def prefixEnd_662003 : Nat := 4983230072969 + 3 ^ 40 * 662003 * 2
def baseEnd_662003 : Nat := 151078103874879397296893

theorem tailTrace_662003 : CollatzResearch.WordTrace tailWord_662003 prefixEnd_662003 151078103874879397296893 := by
  unfold tailWord_662003
  simp only [CollatzResearch.WordTrace]
  refine ⟨24145233020683666956254663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16096822013789111304169775 24145233020683666956254663)
  ·
    refine ⟨36217849531025500434381995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24145233020683666956254663 36217849531025500434381995)
    ·
      refine ⟨54326774296538250651572993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36217849531025500434381995 54326774296538250651572993)
      ·
        refine ⟨40745080722403687988679745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54326774296538250651572993 40745080722403687988679745)
        ·
          refine ⟨30558810541802765991509809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40745080722403687988679745 30558810541802765991509809)
          ·
            refine ⟨22919107906352074493632357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30558810541802765991509809 22919107906352074493632357)
            ·
              refine ⟨4297332732441013967556067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22919107906352074493632357 4297332732441013967556067)
              ·
                refine ⟨6445999098661520951334101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4297332732441013967556067 6445999098661520951334101)
                ·
                  refine ⟨151078103874879397296893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6445999098661520951334101 151078103874879397296893)
                  ·
                    rfl

theorem cell21_662003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_662003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662003 prefixEnd_662003 := by exact prefixLift 662003
  have htrace : WordTrace (prefixWord ++ tailWord_662003) baseStart_662003 baseEnd_662003 := by
    simpa [prefixWord, tailWord_662003, baseEnd_662003] using wordTrace_append hprefix tailTrace_662003
  have hstable : (prefixWord ++ tailWord_662003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662003).length < 2 ^ (prefixWord ++ tailWord_662003).sum := by decide
  have hdescent : baseEnd_662003 < baseStart_662003 := by decide
  rcases family_descends (prefixWord ++ tailWord_662003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662029 : List Nat := [1, 7, 1, 1, 1, 3, 2, 2, 3]
def baseStart_662029 : Nat := 118140960795 + 662029 * 2 ^ 59
def prefixEnd_662029 : Nat := 4983230072969 + 3 ^ 40 * 662029 * 2
def baseEnd_662029 : Nat := 151084037429109129863507

theorem tailTrace_662029 : CollatzResearch.WordTrace tailWord_662029 prefixEnd_662029 151084037429109129863507 := by
  unfold tailWord_662029
  simp only [CollatzResearch.WordTrace]
  refine ⟨24146181318589473396701141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16097454212392982264467427 24146181318589473396701141)
  ·
    refine ⟨565926124654440782735183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 24146181318589473396701141 565926124654440782735183)
    ·
      refine ⟨848889186981661174102775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565926124654440782735183 848889186981661174102775)
      ·
        refine ⟨1273333780472491761154163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848889186981661174102775 1273333780472491761154163)
        ·
          refine ⟨1910000670708737641731245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1273333780472491761154163 1910000670708737641731245)
          ·
            refine ⟨716250251515776615649217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1910000670708737641731245 716250251515776615649217)
            ·
              refine ⟨537187688636832461736913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716250251515776615649217 537187688636832461736913)
              ·
                refine ⟨402890766477624346302685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537187688636832461736913 402890766477624346302685)
                ·
                  refine ⟨151084037429109129863507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402890766477624346302685 151084037429109129863507)
                  ·
                    rfl

theorem cell21_662029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_662029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662029 prefixEnd_662029 := by exact prefixLift 662029
  have htrace : WordTrace (prefixWord ++ tailWord_662029) baseStart_662029 baseEnd_662029 := by
    simpa [prefixWord, tailWord_662029, baseEnd_662029] using wordTrace_append hprefix tailTrace_662029
  have hstable : (prefixWord ++ tailWord_662029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662029).length < 2 ^ (prefixWord ++ tailWord_662029).sum := by decide
  have hdescent : baseEnd_662029 < baseStart_662029 := by decide
  rcases family_descends (prefixWord ++ tailWord_662029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662037 : List Nat := [1, 3, 2, 1, 3, 1, 3, 4, 3]
def baseStart_662037 : Nat := 118140960795 + 662037 * 2 ^ 59
def prefixEnd_662037 : Nat := 4983230072969 + 3 ^ 40 * 662037 * 2
def baseEnd_662037 : Nat := 151085863138102893730157

theorem tailTrace_662037 : CollatzResearch.WordTrace tailWord_662037 prefixEnd_662037 151085863138102893730157 := by
  unfold tailWord_662037
  simp only [CollatzResearch.WordTrace]
  refine ⟨24146473102560490762992365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16097648735040327175328243 24146473102560490762992365)
  ·
    refine ⟨9054927413460184036122137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24146473102560490762992365 9054927413460184036122137)
    ·
      refine ⟨6791195560095138027091603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9054927413460184036122137 6791195560095138027091603)
      ·
        refine ⟨10186793340142707040637405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6791195560095138027091603 10186793340142707040637405)
        ·
          refine ⟨3820047502553515140239027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10186793340142707040637405 3820047502553515140239027)
          ·
            refine ⟨5730071253830272710358541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3820047502553515140239027 5730071253830272710358541)
            ·
              refine ⟨2148776720186352266384453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5730071253830272710358541 2148776720186352266384453)
              ·
                refine ⟨402895635034941049947085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2148776720186352266384453 402895635034941049947085)
                ·
                  refine ⟨151085863138102893730157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402895635034941049947085 151085863138102893730157)
                  ·
                    rfl

theorem cell21_662037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_662037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662037 prefixEnd_662037 := by exact prefixLift 662037
  have htrace : WordTrace (prefixWord ++ tailWord_662037) baseStart_662037 baseEnd_662037 := by
    simpa [prefixWord, tailWord_662037, baseEnd_662037] using wordTrace_append hprefix tailTrace_662037
  have hstable : (prefixWord ++ tailWord_662037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662037).length < 2 ^ (prefixWord ++ tailWord_662037).sum := by decide
  have hdescent : baseEnd_662037 < baseStart_662037 := by decide
  rcases family_descends (prefixWord ++ tailWord_662037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662051 : List Nat := [1, 1, 1, 4, 4, 1, 2, 3, 4]
def baseStart_662051 : Nat := 118140960795 + 662051 * 2 ^ 59
def prefixEnd_662051 : Nat := 4983230072969 + 3 ^ 40 * 662051 * 2
def baseEnd_662051 : Nat := 151089058128841980496795

theorem tailTrace_662051 : CollatzResearch.WordTrace tailWord_662051 prefixEnd_662051 151089058128841980496795 := by
  unfold tailWord_662051
  simp only [CollatzResearch.WordTrace]
  refine ⟨24146983724509771154002007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16097989149673180769334671 24146983724509771154002007)
  ·
    refine ⟨36220475586764656731003011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24146983724509771154002007 36220475586764656731003011)
    ·
      refine ⟨54330713380146985096504517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36220475586764656731003011 54330713380146985096504517)
      ·
        refine ⟨10187008758777559705594597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54330713380146985096504517 10187008758777559705594597)
        ·
          refine ⟨1910064142270792444798987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10187008758777559705594597 1910064142270792444798987)
          ·
            refine ⟨2865096213406188667198481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1910064142270792444798987 2865096213406188667198481)
            ·
              refine ⟨2148822160054641500398861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2865096213406188667198481 2148822160054641500398861)
              ·
                refine ⟨805808310020490562649573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2148822160054641500398861 805808310020490562649573)
                ·
                  refine ⟨151089058128841980496795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805808310020490562649573 151089058128841980496795)
                  ·
                    rfl

theorem cell21_662051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 4].length) (baseStart_662051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662051 prefixEnd_662051 := by exact prefixLift 662051
  have htrace : WordTrace (prefixWord ++ tailWord_662051) baseStart_662051 baseEnd_662051 := by
    simpa [prefixWord, tailWord_662051, baseEnd_662051] using wordTrace_append hprefix tailTrace_662051
  have hstable : (prefixWord ++ tailWord_662051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662051).length < 2 ^ (prefixWord ++ tailWord_662051).sum := by decide
  have hdescent : baseEnd_662051 < baseStart_662051 := by decide
  rcases family_descends (prefixWord ++ tailWord_662051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662079 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 7]
def baseStart_662079 : Nat := 118140960795 + 662079 * 2 ^ 59
def prefixEnd_662079 : Nat := 4983230072969 + 3 ^ 40 * 662079 * 2
def baseEnd_662079 : Nat := 151095448110320154030071

theorem tailTrace_662079 : CollatzResearch.WordTrace tailWord_662079 prefixEnd_662079 151095448110320154030071 := by
  unfold tailWord_662079
  simp only [CollatzResearch.WordTrace]
  refine ⟨24148004968408331936021291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16098669978938887957347527 24148004968408331936021291)
  ·
    refine ⟨36222007452612497904031937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24148004968408331936021291 36222007452612497904031937)
    ·
      refine ⟨27166505589459373428023953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36222007452612497904031937 27166505589459373428023953)
      ·
        refine ⟨20374879192094530071017965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27166505589459373428023953 20374879192094530071017965)
        ·
          refine ⟨7640579697035448776631737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20374879192094530071017965 7640579697035448776631737)
          ·
            refine ⟨5730434772776586582473803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7640579697035448776631737 5730434772776586582473803)
            ·
              refine ⟨8595652159164879873710705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5730434772776586582473803 8595652159164879873710705)
              ·
                refine ⟨6446739119373659905283029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8595652159164879873710705 6446739119373659905283029)
                ·
                  refine ⟨151095448110320154030071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6446739119373659905283029 151095448110320154030071)
                  ·
                    rfl

theorem cell21_662079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_662079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662079 prefixEnd_662079 := by exact prefixLift 662079
  have htrace : WordTrace (prefixWord ++ tailWord_662079) baseStart_662079 baseEnd_662079 := by
    simpa [prefixWord, tailWord_662079, baseEnd_662079] using wordTrace_append hprefix tailTrace_662079
  have hstable : (prefixWord ++ tailWord_662079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662079).length < 2 ^ (prefixWord ++ tailWord_662079).sum := by decide
  have hdescent : baseEnd_662079 < baseStart_662079 := by decide
  rcases family_descends (prefixWord ++ tailWord_662079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662155 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 5]
def baseStart_662155 : Nat := 118140960795 + 662155 * 2 ^ 59
def prefixEnd_662155 : Nat := 4983230072969 + 3 ^ 40 * 662155 * 2
def baseEnd_662155 : Nat := 151112792345760910763249

theorem tailTrace_662155 : CollatzResearch.WordTrace tailWord_662155 prefixEnd_662155 151112792345760910763249 := by
  unfold tailWord_662155
  simp only [CollatzResearch.WordTrace]
  refine ⟨24150776916132996915787919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16100517944088664610525279 24150776916132996915787919)
  ·
    refine ⟨36226165374199495373681879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24150776916132996915787919 36226165374199495373681879)
    ·
      refine ⟨54339248061299243060522819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36226165374199495373681879 54339248061299243060522819)
      ·
        refine ⟨81508872091948864590784229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54339248061299243060522819 81508872091948864590784229)
        ·
          refine ⟨15282913517240412110772043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81508872091948864590784229 15282913517240412110772043)
          ·
            refine ⟨22924370275860618166158065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15282913517240412110772043 22924370275860618166158065)
            ·
              refine ⟨17193277706895463624618549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22924370275860618166158065 17193277706895463624618549)
              ·
                refine ⟨1611869785021449714807989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17193277706895463624618549 1611869785021449714807989)
                ·
                  refine ⟨151112792345760910763249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1611869785021449714807989 151112792345760910763249)
                  ·
                    rfl

theorem cell21_662155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 5].length) (baseStart_662155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662155 prefixEnd_662155 := by exact prefixLift 662155
  have htrace : WordTrace (prefixWord ++ tailWord_662155) baseStart_662155 baseEnd_662155 := by
    simpa [prefixWord, tailWord_662155, baseEnd_662155] using wordTrace_append hprefix tailTrace_662155
  have hstable : (prefixWord ++ tailWord_662155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662155).length < 2 ^ (prefixWord ++ tailWord_662155).sum := by decide
  have hdescent : baseEnd_662155 < baseStart_662155 := by decide
  rcases family_descends (prefixWord ++ tailWord_662155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662231 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 7]
def baseStart_662231 : Nat := 118140960795 + 662231 * 2 ^ 59
def prefixEnd_662231 : Nat := 4983230072969 + 3 ^ 40 * 662231 * 2
def baseEnd_662231 : Nat := 151130136581201667496427

theorem tailTrace_662231 : CollatzResearch.WordTrace tailWord_662231 prefixEnd_662231 151130136581201667496427 := by
  unfold tailWord_662231
  simp only [CollatzResearch.WordTrace]
  refine ⟨24153548863857661895554547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16102365909238441263703031 24153548863857661895554547)
  ·
    refine ⟨36230323295786492843331821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24153548863857661895554547 36230323295786492843331821)
    ·
      refine ⟨13586371235919934816249433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36230323295786492843331821 13586371235919934816249433)
      ·
        refine ⟨10189778426939951112187075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13586371235919934816249433 10189778426939951112187075)
        ·
          refine ⟨15284667640409926668280613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10189778426939951112187075 15284667640409926668280613)
          ·
            refine ⟨2865875182576861250302615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15284667640409926668280613 2865875182576861250302615)
            ·
              refine ⟨4298812773865291875453923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2865875182576861250302615 4298812773865291875453923)
              ·
                refine ⟨6448219160797937813180885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4298812773865291875453923 6448219160797937813180885)
                ·
                  refine ⟨151130136581201667496427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6448219160797937813180885 151130136581201667496427)
                  ·
                    rfl

theorem cell21_662231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_662231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662231 prefixEnd_662231 := by exact prefixLift 662231
  have htrace : WordTrace (prefixWord ++ tailWord_662231) baseStart_662231 baseEnd_662231 := by
    simpa [prefixWord, tailWord_662231, baseEnd_662231] using wordTrace_append hprefix tailTrace_662231
  have hstable : (prefixWord ++ tailWord_662231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662231).length < 2 ^ (prefixWord ++ tailWord_662231).sum := by decide
  have hdescent : baseEnd_662231 < baseStart_662231 := by decide
  rcases family_descends (prefixWord ++ tailWord_662231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662352 : List Nat := [2, 1, 1, 1, 1, 4, 4, 7]
def baseStart_662352 : Nat := 118140960795 + 662352 * 2 ^ 59
def prefixEnd_662352 : Nat := 4983230072969 + 3 ^ 40 * 662352 * 2
def baseEnd_662352 : Nat := 50385916809910781993171

theorem tailTrace_662352 : CollatzResearch.WordTrace tailWord_662352 prefixEnd_662352 50385916809910781993171 := by
  unfold tailWord_662352
  simp only [CollatzResearch.WordTrace]
  refine ⟨12078981048209649780354655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16105308064279533040472873 12078981048209649780354655)
  ·
    refine ⟨18118471572314474670531983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12078981048209649780354655 18118471572314474670531983)
    ·
      refine ⟨27177707358471712005797975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18118471572314474670531983 27177707358471712005797975)
      ·
        refine ⟨40766561037707568008696963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27177707358471712005797975 40766561037707568008696963)
        ·
          refine ⟨61149841556561352013045445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40766561037707568008696963 61149841556561352013045445)
          ·
            refine ⟨11465595291855253502446021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61149841556561352013045445 11465595291855253502446021)
            ·
              refine ⟨2149799117222860031708629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11465595291855253502446021 2149799117222860031708629)
              ·
                refine ⟨50385916809910781993171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2149799117222860031708629 50385916809910781993171)
                ·
                  rfl

theorem cell21_662352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_662352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662352 prefixEnd_662352 := by exact prefixLift 662352
  have htrace : WordTrace (prefixWord ++ tailWord_662352) baseStart_662352 baseEnd_662352 := by
    simpa [prefixWord, tailWord_662352, baseEnd_662352] using wordTrace_append hprefix tailTrace_662352
  have hstable : (prefixWord ++ tailWord_662352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662352).length < 2 ^ (prefixWord ++ tailWord_662352).sum := by decide
  have hdescent : baseEnd_662352 < baseStart_662352 := by decide
  rcases family_descends (prefixWord ++ tailWord_662352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662431 : List Nat := [1, 1, 2, 5, 2, 1, 3, 2, 4]
def baseStart_662431 : Nat := 118140960795 + 662431 * 2 ^ 59
def prefixEnd_662431 : Nat := 4983230072969 + 3 ^ 40 * 662431 * 2
def baseEnd_662431 : Nat := 151175779306045764162685

theorem tailTrace_662431 : CollatzResearch.WordTrace tailWord_662431 prefixEnd_662431 151175779306045764162685 := by
  unfold tailWord_662431
  simp only [CollatzResearch.WordTrace]
  refine ⟨24160843463133096052835147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16107228975422064035223431 24160843463133096052835147)
  ·
    refine ⟨36241265194699644079252721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24160843463133096052835147 36241265194699644079252721)
    ·
      refine ⟨27180948896024733059439541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36241265194699644079252721 27180948896024733059439541)
      ·
        refine ⟨2548213959002318724322457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27180948896024733059439541 2548213959002318724322457)
        ·
          refine ⟨1911160469251739043241843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2548213959002318724322457 1911160469251739043241843)
          ·
            refine ⟨2866740703877608564862765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911160469251739043241843 2866740703877608564862765)
            ·
              refine ⟨1075027763954103211823537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2866740703877608564862765 1075027763954103211823537)
              ·
                refine ⟨806270822965577408867653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075027763954103211823537 806270822965577408867653)
                ·
                  refine ⟨151175779306045764162685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 806270822965577408867653 151175779306045764162685)
                  ·
                    rfl

theorem cell21_662431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 4].length) (baseStart_662431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662431 prefixEnd_662431 := by exact prefixLift 662431
  have htrace : WordTrace (prefixWord ++ tailWord_662431) baseStart_662431 baseEnd_662431 := by
    simpa [prefixWord, tailWord_662431, baseEnd_662431] using wordTrace_append hprefix tailTrace_662431
  have hstable : (prefixWord ++ tailWord_662431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662431).length < 2 ^ (prefixWord ++ tailWord_662431).sum := by decide
  have hdescent : baseEnd_662431 < baseStart_662431 := by decide
  rcases family_descends (prefixWord ++ tailWord_662431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662454 : List Nat := [5, 1, 4, 1, 2, 1, 2, 5]
def baseStart_662454 : Nat := 118140960795 + 662454 * 2 ^ 59
def prefixEnd_662454 : Nat := 4983230072969 + 3 ^ 40 * 662454 * 2
def baseEnd_662454 : Nat := 50393676073134278426435

theorem tailTrace_662454 : CollatzResearch.WordTrace tailWord_662454 prefixEnd_662454 50393676073134278426435 := by
  unfold tailWord_662454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1510105146378110686307651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16107788228033180653948277 1510105146378110686307651)
  ·
    refine ⟨2265157719567166029461477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1510105146378110686307651 2265157719567166029461477)
    ·
      refine ⟨424717072418843630524027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2265157719567166029461477 424717072418843630524027)
      ·
        refine ⟨637075608628265445786041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424717072418843630524027 637075608628265445786041)
        ·
          refine ⟨477806706471199084339531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637075608628265445786041 477806706471199084339531)
          ·
            refine ⟨716710059706798626509297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477806706471199084339531 716710059706798626509297)
            ·
              refine ⟨537532544780098969881973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716710059706798626509297 537532544780098969881973)
              ·
                refine ⟨50393676073134278426435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 537532544780098969881973 50393676073134278426435)
                ·
                  rfl

theorem cell21_662454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_662454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662454 prefixEnd_662454 := by exact prefixLift 662454
  have htrace : WordTrace (prefixWord ++ tailWord_662454) baseStart_662454 baseEnd_662454 := by
    simpa [prefixWord, tailWord_662454, baseEnd_662454] using wordTrace_append hprefix tailTrace_662454
  have hstable : (prefixWord ++ tailWord_662454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662454).length < 2 ^ (prefixWord ++ tailWord_662454).sum := by decide
  have hdescent : baseEnd_662454 < baseStart_662454 := by decide
  rcases family_descends (prefixWord ++ tailWord_662454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662468 : List Nat := [2, 3, 3, 3, 2, 1, 1, 3, 3]
def baseStart_662468 : Nat := 118140960795 + 662468 * 2 ^ 59
def prefixEnd_662468 : Nat := 4983230072969 + 3 ^ 40 * 662468 * 2
def baseEnd_662468 : Nat := 151184223210141922045943

theorem tailTrace_662468 : CollatzResearch.WordTrace tailWord_662468 prefixEnd_662468 151184223210141922045943 := by
  unfold tailWord_662468
  simp only [CollatzResearch.WordTrace]
  refine ⟨12081096481999525685966029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16108128642666034247954705 12081096481999525685966029)
  ·
    refine ⟨4530411180749822132237261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12081096481999525685966029 4530411180749822132237261)
    ·
      refine ⟨1698904192781183299588973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4530411180749822132237261 1698904192781183299588973)
      ·
        refine ⟨637089072292943737345865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1698904192781183299588973 637089072292943737345865)
        ·
          refine ⟨477816804219707803009399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637089072292943737345865 477816804219707803009399)
          ·
            refine ⟨716725206329561704514099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477816804219707803009399 716725206329561704514099)
            ·
              refine ⟨1075087809494342556771149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716725206329561704514099 1075087809494342556771149)
              ·
                refine ⟨403157928560378458789181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1075087809494342556771149 403157928560378458789181)
                ·
                  refine ⟨151184223210141922045943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403157928560378458789181 151184223210141922045943)
                  ·
                    rfl

theorem cell21_662468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_662468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662468 prefixEnd_662468 := by exact prefixLift 662468
  have htrace : WordTrace (prefixWord ++ tailWord_662468) baseStart_662468 baseEnd_662468 := by
    simpa [prefixWord, tailWord_662468, baseEnd_662468] using wordTrace_append hprefix tailTrace_662468
  have hstable : (prefixWord ++ tailWord_662468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662468).length < 2 ^ (prefixWord ++ tailWord_662468).sum := by decide
  have hdescent : baseEnd_662468 < baseStart_662468 := by decide
  rcases family_descends (prefixWord ++ tailWord_662468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662490 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_662490 : Nat := 118140960795 + 662490 * 2 ^ 59
def prefixEnd_662490 : Nat := 4983230072969 + 3 ^ 40 * 662490 * 2
def baseEnd_662490 : Nat := 151189243909874772679231

theorem tailTrace_662490 : CollatzResearch.WordTrace tailWord_662490 prefixEnd_662490 151189243909874772679231 := by
  unfold tailWord_662490
  simp only [CollatzResearch.WordTrace]
  refine ⟨6040748842479837282308231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16108663579946232752821949 6040748842479837282308231)
  ·
    refine ⟨9061123263719755923462347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6040748842479837282308231 9061123263719755923462347)
    ·
      refine ⟨13591684895579633885193521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9061123263719755923462347 13591684895579633885193521)
      ·
        refine ⟨10193763671684725413895141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13591684895579633885193521 10193763671684725413895141)
        ·
          refine ⟨1911330688440886015105339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10193763671684725413895141 1911330688440886015105339)
          ·
            refine ⟨2866996032661329022658009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911330688440886015105339 2866996032661329022658009)
            ·
              refine ⟨2150247024495996766993507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2866996032661329022658009 2150247024495996766993507)
              ·
                refine ⟨3225370536743995150490261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2150247024495996766993507 3225370536743995150490261)
                ·
                  refine ⟨151189243909874772679231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3225370536743995150490261 151189243909874772679231)
                  ·
                    rfl

theorem cell21_662490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_662490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662490 prefixEnd_662490 := by exact prefixLift 662490
  have htrace : WordTrace (prefixWord ++ tailWord_662490) baseStart_662490 baseEnd_662490 := by
    simpa [prefixWord, tailWord_662490, baseEnd_662490] using wordTrace_append hprefix tailTrace_662490
  have hstable : (prefixWord ++ tailWord_662490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662490).length < 2 ^ (prefixWord ++ tailWord_662490).sum := by decide
  have hdescent : baseEnd_662490 < baseStart_662490 := by decide
  rcases family_descends (prefixWord ++ tailWord_662490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662493 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 5]
def baseStart_662493 : Nat := 118140960795 + 662493 * 2 ^ 59
def prefixEnd_662493 : Nat := 4983230072969 + 3 ^ 40 * 662493 * 2
def baseEnd_662493 : Nat := 151189928550747434129225

theorem tailTrace_662493 : CollatzResearch.WordTrace tailWord_662493 prefixEnd_662493 151189928550747434129225 := by
  unfold tailWord_662493
  simp only [CollatzResearch.WordTrace]
  refine ⟨24163104788908480641592133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16108736525938987094394755 24163104788908480641592133)
  ·
    refine ⟨4530582147920340120298525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24163104788908480641592133 4530582147920340120298525)
    ·
      refine ⟨1698968305470127545111947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4530582147920340120298525 1698968305470127545111947)
      ·
        refine ⟨2548452458205191317667921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1698968305470127545111947 2548452458205191317667921)
        ·
          refine ⟨1911339343653893488250941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2548452458205191317667921 1911339343653893488250941)
          ·
            refine ⟨716752253870210058094103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1911339343653893488250941 716752253870210058094103)
            ·
              refine ⟨1075128380805315087141155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716752253870210058094103 1075128380805315087141155)
              ·
                refine ⟨1612692571207972630711733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075128380805315087141155 1612692571207972630711733)
                ·
                  refine ⟨151189928550747434129225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1612692571207972630711733 151189928550747434129225)
                  ·
                    rfl

theorem cell21_662493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_662493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662493 prefixEnd_662493 := by exact prefixLift 662493
  have htrace : WordTrace (prefixWord ++ tailWord_662493) baseStart_662493 baseEnd_662493 := by
    simpa [prefixWord, tailWord_662493, baseEnd_662493] using wordTrace_append hprefix tailTrace_662493
  have hstable : (prefixWord ++ tailWord_662493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662493).length < 2 ^ (prefixWord ++ tailWord_662493).sum := by decide
  have hdescent : baseEnd_662493 < baseStart_662493 := by decide
  rcases family_descends (prefixWord ++ tailWord_662493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662504 : List Nat := [2, 1, 4, 1, 1, 1, 3, 8]
def baseStart_662504 : Nat := 118140960795 + 662504 * 2 ^ 59
def prefixEnd_662504 : Nat := 4983230072969 + 3 ^ 40 * 662504 * 2
def baseEnd_662504 : Nat := 50397479633537953148623

theorem tailTrace_662504 : CollatzResearch.WordTrace tailWord_662504 prefixEnd_662504 50397479633537953148623 := by
  unfold tailWord_662504
  simp only [CollatzResearch.WordTrace]
  refine ⟨12081752995934314760121283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16109003994579086346828377 12081752995934314760121283)
  ·
    refine ⟨18122629493901472140181925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12081752995934314760121283 18122629493901472140181925)
    ·
      refine ⟨3397993030106526026284111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18122629493901472140181925 3397993030106526026284111)
      ·
        refine ⟨5096989545159789039426167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3397993030106526026284111 5096989545159789039426167)
        ·
          refine ⟨7645484317739683559139251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5096989545159789039426167 7645484317739683559139251)
          ·
            refine ⟨11468226476609525338708877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7645484317739683559139251 11468226476609525338708877)
            ·
              refine ⟨4300584928728572002015829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11468226476609525338708877 4300584928728572002015829)
              ·
                refine ⟨50397479633537953148623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4300584928728572002015829 50397479633537953148623)
                ·
                  rfl

theorem cell21_662504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_662504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662504 prefixEnd_662504 := by exact prefixLift 662504
  have htrace : WordTrace (prefixWord ++ tailWord_662504) baseStart_662504 baseEnd_662504 := by
    simpa [prefixWord, tailWord_662504, baseEnd_662504] using wordTrace_append hprefix tailTrace_662504
  have hstable : (prefixWord ++ tailWord_662504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662504).length < 2 ^ (prefixWord ++ tailWord_662504).sum := by decide
  have hdescent : baseEnd_662504 < baseStart_662504 := by decide
  rcases family_descends (prefixWord ++ tailWord_662504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662777 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 6]
def baseStart_662777 : Nat := 118140960795 + 662777 * 2 ^ 59
def prefixEnd_662777 : Nat := 4983230072969 + 3 ^ 40 * 662777 * 2
def baseEnd_662777 : Nat := 151254741220026051395311

theorem tailTrace_662777 : CollatzResearch.WordTrace tailWord_662777 prefixEnd_662777 151254741220026051395311 := by
  unfold tailWord_662777
  simp only [CollatzResearch.WordTrace]
  refine ⟨24173463119879597144930585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16115642079919731429953723 24173463119879597144930585)
  ·
    refine ⟨18130097339909697858697939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24173463119879597144930585 18130097339909697858697939)
    ·
      refine ⟨27195146009864546788046909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18130097339909697858697939 27195146009864546788046909)
      ·
        refine ⟨10198179753699205045517591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27195146009864546788046909 10198179753699205045517591)
        ·
          refine ⟨15297269630548807568276387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10198179753699205045517591 15297269630548807568276387)
          ·
            refine ⟨22945904445823211352414581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15297269630548807568276387 22945904445823211352414581)
            ·
              refine ⟨2151178541795926064288867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22945904445823211352414581 2151178541795926064288867)
              ·
                refine ⟨3226767812693889096433301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151178541795926064288867 3226767812693889096433301)
                ·
                  refine ⟨151254741220026051395311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3226767812693889096433301 151254741220026051395311)
                  ·
                    rfl

theorem cell21_662777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_662777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662777 prefixEnd_662777 := by exact prefixLift 662777
  have htrace : WordTrace (prefixWord ++ tailWord_662777) baseStart_662777 baseEnd_662777 := by
    simpa [prefixWord, tailWord_662777, baseEnd_662777] using wordTrace_append hprefix tailTrace_662777
  have hstable : (prefixWord ++ tailWord_662777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662777).length < 2 ^ (prefixWord ++ tailWord_662777).sum := by decide
  have hdescent : baseEnd_662777 < baseStart_662777 := by decide
  rcases family_descends (prefixWord ++ tailWord_662777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662780 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 5]
def baseStart_662780 : Nat := 118140960795 + 662780 * 2 ^ 59
def prefixEnd_662780 : Nat := 4983230072969 + 3 ^ 40 * 662780 * 2
def baseEnd_662780 : Nat := 151255425860898712845305

theorem tailTrace_662780 : CollatzResearch.WordTrace tailWord_662780 prefixEnd_662780 151255425860898712845305 := by
  unfold tailWord_662780
  simp only [CollatzResearch.WordTrace]
  refine ⟨12086786269434364328644897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16115715025912485771526529 12086786269434364328644897)
  ·
    refine ⟨9065089702075773246483673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12086786269434364328644897 9065089702075773246483673)
    ·
      refine ⟨6798817276556829934862755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9065089702075773246483673 6798817276556829934862755)
      ·
        refine ⟨10198225914835244902294133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6798817276556829934862755 10198225914835244902294133)
        ·
          refine ⟨956083679515804209590075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10198225914835244902294133 956083679515804209590075)
          ·
            refine ⟨1434125519273706314385113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956083679515804209590075 1434125519273706314385113)
            ·
              refine ⟨1075594139455279735788835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1434125519273706314385113 1075594139455279735788835)
              ·
                refine ⟨1613391209182919603683253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075594139455279735788835 1613391209182919603683253)
                ·
                  refine ⟨151255425860898712845305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1613391209182919603683253 151255425860898712845305)
                  ·
                    rfl

theorem cell21_662780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_662780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662780 prefixEnd_662780 := by exact prefixLift 662780
  have htrace : WordTrace (prefixWord ++ tailWord_662780) baseStart_662780 baseEnd_662780 := by
    simpa [prefixWord, tailWord_662780, baseEnd_662780] using wordTrace_append hprefix tailTrace_662780
  have hstable : (prefixWord ++ tailWord_662780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662780).length < 2 ^ (prefixWord ++ tailWord_662780).sum := by decide
  have hdescent : baseEnd_662780 < baseStart_662780 := by decide
  rcases family_descends (prefixWord ++ tailWord_662780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662808 : List Nat := [2, 1, 2, 3, 1, 4, 1, 7]
def baseStart_662808 : Nat := 118140960795 + 662808 * 2 ^ 59
def prefixEnd_662808 : Nat := 4983230072969 + 3 ^ 40 * 662808 * 2
def baseEnd_662808 : Nat := 50420605280792295459527

theorem tailTrace_662808 : CollatzResearch.WordTrace tailWord_662808 prefixEnd_662808 50420605280792295459527 := by
  unfold tailWord_662808
  simp only [CollatzResearch.WordTrace]
  refine ⟨12087296891383644719654539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16116395855178192959539385 12087296891383644719654539)
  ·
    refine ⟨18130945337075467079481809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12087296891383644719654539 18130945337075467079481809)
    ·
      refine ⟨13598209002806600309611357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18130945337075467079481809 13598209002806600309611357)
      ·
        refine ⟨5099328376052475116104259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13598209002806600309611357 5099328376052475116104259)
        ·
          refine ⟨7648992564078712674156389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5099328376052475116104259 7648992564078712674156389)
          ·
            refine ⟨1434186105764758626404323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7648992564078712674156389 1434186105764758626404323)
            ·
              refine ⟨2151279158647137939606485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434186105764758626404323 2151279158647137939606485)
              ·
                refine ⟨50420605280792295459527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2151279158647137939606485 50420605280792295459527)
                ·
                  rfl

theorem cell21_662808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_662808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662808 prefixEnd_662808 := by exact prefixLift 662808
  have htrace : WordTrace (prefixWord ++ tailWord_662808) baseStart_662808 baseEnd_662808 := by
    simpa [prefixWord, tailWord_662808, baseEnd_662808] using wordTrace_append hprefix tailTrace_662808
  have hstable : (prefixWord ++ tailWord_662808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662808).length < 2 ^ (prefixWord ++ tailWord_662808).sum := by decide
  have hdescent : baseEnd_662808 < baseStart_662808 := by decide
  rcases family_descends (prefixWord ++ tailWord_662808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662845 : List Nat := [1, 4, 1, 5, 1, 2, 2, 1, 4]
def baseStart_662845 : Nat := 118140960795 + 662845 * 2 ^ 59
def prefixEnd_662845 : Nat := 4983230072969 + 3 ^ 40 * 662845 * 2
def baseEnd_662845 : Nat := 151270259746473044261839

theorem tailTrace_662845 : CollatzResearch.WordTrace tailWord_662845 prefixEnd_662845 151270259746473044261839 := by
  unfold tailWord_662845
  simp only [CollatzResearch.WordTrace]
  refine ⟨24175943283633244758405989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16117295522422163172270659 24175943283633244758405989)
  ·
    refine ⟨4532989365681233392201123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24175943283633244758405989 4532989365681233392201123)
    ·
      refine ⟨6799484048521850088301685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4532989365681233392201123 6799484048521850088301685)
      ·
        refine ⟨637451629548923445778283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6799484048521850088301685 637451629548923445778283)
        ·
          refine ⟨956177444323385168667425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637451629548923445778283 956177444323385168667425)
          ·
            refine ⟨717133083242538876500569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 956177444323385168667425 717133083242538876500569)
            ·
              refine ⟨537849812431904157375427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 717133083242538876500569 537849812431904157375427)
              ·
                refine ⟨806774718647856236063141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537849812431904157375427 806774718647856236063141)
                ·
                  refine ⟨151270259746473044261839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 806774718647856236063141 151270259746473044261839)
                  ·
                    rfl

theorem cell21_662845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_662845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662845 prefixEnd_662845 := by exact prefixLift 662845
  have htrace : WordTrace (prefixWord ++ tailWord_662845) baseStart_662845 baseEnd_662845 := by
    simpa [prefixWord, tailWord_662845, baseEnd_662845] using wordTrace_append hprefix tailTrace_662845
  have hstable : (prefixWord ++ tailWord_662845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662845).length < 2 ^ (prefixWord ++ tailWord_662845).sum := by decide
  have hdescent : baseEnd_662845 < baseStart_662845 := by decide
  rcases family_descends (prefixWord ++ tailWord_662845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662867 : List Nat := [1, 1, 1, 2, 1, 1, 5, 9]
def baseStart_662867 : Nat := 118140960795 + 662867 * 2 ^ 59
def prefixEnd_662867 : Nat := 4983230072969 + 3 ^ 40 * 662867 * 2
def baseEnd_662867 : Nat := 50425093482068631631709

theorem tailTrace_662867 : CollatzResearch.WordTrace tailWord_662867 prefixEnd_662867 50425093482068631631709 := by
  unfold tailWord_662867
  simp only [CollatzResearch.WordTrace]
  refine ⟨24176745689553542515706855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16117830459702361677137903 24176745689553542515706855)
  ·
    refine ⟨36265118534330313773560283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24176745689553542515706855 36265118534330313773560283)
    ·
      refine ⟨54397677801495470660340425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36265118534330313773560283 54397677801495470660340425)
      ·
        refine ⟨40798258351121602995255319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54397677801495470660340425 40798258351121602995255319)
        ·
          refine ⟨61197387526682404492882979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40798258351121602995255319 61197387526682404492882979)
          ·
            refine ⟨91796081290023606739324469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61197387526682404492882979 91796081290023606739324469)
            ·
              refine ⟨8605882620939713131811669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91796081290023606739324469 8605882620939713131811669)
              ·
                refine ⟨50425093482068631631709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8605882620939713131811669 50425093482068631631709)
                ·
                  rfl

theorem cell21_662867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 9].length) (baseStart_662867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662867 prefixEnd_662867 := by exact prefixLift 662867
  have htrace : WordTrace (prefixWord ++ tailWord_662867) baseStart_662867 baseEnd_662867 := by
    simpa [prefixWord, tailWord_662867, baseEnd_662867] using wordTrace_append hprefix tailTrace_662867
  have hstable : (prefixWord ++ tailWord_662867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662867).length < 2 ^ (prefixWord ++ tailWord_662867).sum := by decide
  have hdescent : baseEnd_662867 < baseStart_662867 := by decide
  rcases family_descends (prefixWord ++ tailWord_662867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662887 : List Nat := [1, 1, 5, 1, 4, 1, 2, 2, 4]
def baseStart_662887 : Nat := 118140960795 + 662887 * 2 ^ 59
def prefixEnd_662887 : Nat := 4983230072969 + 3 ^ 40 * 662887 * 2
def baseEnd_662887 : Nat := 151279844718690304561753

theorem tailTrace_662887 : CollatzResearch.WordTrace tailWord_662887 prefixEnd_662887 151279844718690304561753 := by
  unfold tailWord_662887
  simp only [CollatzResearch.WordTrace]
  refine ⟨24177475149481085931434915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16118316766320723954289943 24177475149481085931434915)
  ·
    refine ⟨36266212724221628897152373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24177475149481085931434915 36266212724221628897152373)
    ·
      refine ⟨3399957442895777709108035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36266212724221628897152373 3399957442895777709108035)
      ·
        refine ⟨5099936164343666563662053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399957442895777709108035 5099936164343666563662053)
        ·
          refine ⟨956238030814437480686635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5099936164343666563662053 956238030814437480686635)
          ·
            refine ⟨1434357046221656221029953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956238030814437480686635 1434357046221656221029953)
            ·
              refine ⟨1075767784666242165772465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1434357046221656221029953 1075767784666242165772465)
              ·
                refine ⟨806825838499681624329349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075767784666242165772465 806825838499681624329349)
                ·
                  refine ⟨151279844718690304561753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 806825838499681624329349 151279844718690304561753)
                  ·
                    rfl

theorem cell21_662887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 4].length) (baseStart_662887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662887 prefixEnd_662887 := by exact prefixLift 662887
  have htrace : WordTrace (prefixWord ++ tailWord_662887) baseStart_662887 baseEnd_662887 := by
    simpa [prefixWord, tailWord_662887, baseEnd_662887] using wordTrace_append hprefix tailTrace_662887
  have hstable : (prefixWord ++ tailWord_662887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662887).length < 2 ^ (prefixWord ++ tailWord_662887).sum := by decide
  have hdescent : baseEnd_662887 < baseStart_662887 := by decide
  rcases family_descends (prefixWord ++ tailWord_662887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662915 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 5]
def baseStart_662915 : Nat := 118140960795 + 662915 * 2 ^ 59
def prefixEnd_662915 : Nat := 4983230072969 + 3 ^ 40 * 662915 * 2
def baseEnd_662915 : Nat := 151286234700168478095029

theorem tailTrace_662915 : CollatzResearch.WordTrace tailWord_662915 prefixEnd_662915 151286234700168478095029 := by
  unfold tailWord_662915
  simp only [CollatzResearch.WordTrace]
  refine ⟨24178496393379646713454199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16118997595586431142302799 24178496393379646713454199)
  ·
    refine ⟨36267744590069470070181299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24178496393379646713454199 36267744590069470070181299)
    ·
      refine ⟨54401616885104205105271949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36267744590069470070181299 54401616885104205105271949)
      ·
        refine ⟨20400606331914076914476981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54401616885104205105271949 20400606331914076914476981)
        ·
          refine ⟨1912556843616944710732217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20400606331914076914476981 1912556843616944710732217)
          ·
            refine ⟨1434417632712708533049163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1912556843616944710732217 1434417632712708533049163)
            ·
              refine ⟨2151626449069062799573745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434417632712708533049163 2151626449069062799573745)
              ·
                refine ⟨1613719836801797099680309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2151626449069062799573745 1613719836801797099680309)
                ·
                  refine ⟨151286234700168478095029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1613719836801797099680309 151286234700168478095029)
                  ·
                    rfl

theorem cell21_662915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 5].length) (baseStart_662915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662915 prefixEnd_662915 := by exact prefixLift 662915
  have htrace : WordTrace (prefixWord ++ tailWord_662915) baseStart_662915 baseEnd_662915 := by
    simpa [prefixWord, tailWord_662915, baseEnd_662915] using wordTrace_append hprefix tailTrace_662915
  have hstable : (prefixWord ++ tailWord_662915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662915).length < 2 ^ (prefixWord ++ tailWord_662915).sum := by decide
  have hdescent : baseEnd_662915 < baseStart_662915 := by decide
  rcases family_descends (prefixWord ++ tailWord_662915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662946 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_662946 : Nat := 118140960795 + 662946 * 2 ^ 59
def prefixEnd_662946 : Nat := 4983230072969 + 3 ^ 40 * 662946 * 2
def baseEnd_662946 : Nat := 151293309322519313078299

theorem tailTrace_662946 : CollatzResearch.WordTrace tailWord_662946 prefixEnd_662946 151293309322519313078299 := by
  unfold tailWord_662946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6044906764066834751958173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16119751370844892671888461 6044906764066834751958173)
  ·
    refine ⟨2266840036525063031984315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6044906764066834751958173 2266840036525063031984315)
    ·
      refine ⟨3400260054787594547976473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2266840036525063031984315 3400260054787594547976473)
      ·
        refine ⟨2550195041090695910982355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3400260054787594547976473 2550195041090695910982355)
        ·
          refine ⟨3825292561636043866473533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550195041090695910982355 3825292561636043866473533)
          ·
            refine ⟨1434484710613516449927575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3825292561636043866473533 1434484710613516449927575)
            ·
              refine ⟨2151727065920274674891363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434484710613516449927575 2151727065920274674891363)
              ·
                refine ⟨3227590598880412012337045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151727065920274674891363 3227590598880412012337045)
                ·
                  refine ⟨151293309322519313078299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3227590598880412012337045 151293309322519313078299)
                  ·
                    rfl

theorem cell21_662946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_662946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_662946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_662946 prefixEnd_662946 := by exact prefixLift 662946
  have htrace : WordTrace (prefixWord ++ tailWord_662946) baseStart_662946 baseEnd_662946 := by
    simpa [prefixWord, tailWord_662946, baseEnd_662946] using wordTrace_append hprefix tailTrace_662946
  have hstable : (prefixWord ++ tailWord_662946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662946).length < 2 ^ (prefixWord ++ tailWord_662946).sum := by decide
  have hdescent : baseEnd_662946 < baseStart_662946 := by decide
  rcases family_descends (prefixWord ++ tailWord_662946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663022 : List Nat := [4, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_663022 : Nat := 118140960795 + 663022 * 2 ^ 59
def prefixEnd_663022 : Nat := 4983230072969 + 3 ^ 40 * 663022 * 2
def baseEnd_663022 : Nat := 151310653557960069811477

theorem tailTrace_663022 : CollatzResearch.WordTrace tailWord_663022 prefixEnd_663022 151310653557960069811477 := by
  unfold tailWord_663022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3022799875499000498449915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16121599335994669325066213 3022799875499000498449915)
  ·
    refine ⟨4534199813248500747674873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3022799875499000498449915 4534199813248500747674873)
    ·
      refine ⟨3400649859936375560756155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4534199813248500747674873 3400649859936375560756155)
      ·
        refine ⟨5100974789904563341134233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3400649859936375560756155 5100974789904563341134233)
        ·
          refine ⟨3825731092428422505850675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5100974789904563341134233 3825731092428422505850675)
          ·
            refine ⟨5738596638642633758776013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3825731092428422505850675 5738596638642633758776013)
            ·
              refine ⟨2151973739490987659541005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5738596638642633758776013 2151973739490987659541005)
              ·
                refine ⟨806990152309120372327877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2151973739490987659541005 806990152309120372327877)
                ·
                  refine ⟨151310653557960069811477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 806990152309120372327877 151310653557960069811477)
                  ·
                    rfl

theorem cell21_663022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_663022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663022 prefixEnd_663022 := by exact prefixLift 663022
  have htrace : WordTrace (prefixWord ++ tailWord_663022) baseStart_663022 baseEnd_663022 := by
    simpa [prefixWord, tailWord_663022, baseEnd_663022] using wordTrace_append hprefix tailTrace_663022
  have hstable : (prefixWord ++ tailWord_663022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663022).length < 2 ^ (prefixWord ++ tailWord_663022).sum := by decide
  have hdescent : baseEnd_663022 < baseStart_663022 := by decide
  rcases family_descends (prefixWord ++ tailWord_663022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663053 : List Nat := [1, 7, 1, 1, 11]
def baseStart_663053 : Nat := 118140960795 + 663053 * 2 ^ 59
def prefixEnd_663053 : Nat := 4983230072969 + 3 ^ 40 * 663053 * 2
def baseEnd_663053 : Nat := 1868120100991492651787

theorem tailTrace_663053 : CollatzResearch.WordTrace tailWord_663053 prefixEnd_663053 1868120100991492651787 := by
  unfold tailWord_663053
  simp only [CollatzResearch.WordTrace]
  refine ⟨24183529666879696281977813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16122353111253130854651875 24183529666879696281977813)
  ·
    refine ⟨566801476567492881608855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 24183529666879696281977813 566801476567492881608855)
    ·
      refine ⟨850202214851239322413283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 566801476567492881608855 850202214851239322413283)
      ·
        refine ⟨1275303322276858983619925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850202214851239322413283 1275303322276858983619925)
        ·
          refine ⟨1868120100991492651787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1275303322276858983619925 1868120100991492651787)
          ·
            rfl

theorem cell21_663053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 11].length) (baseStart_663053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663053 prefixEnd_663053 := by exact prefixLift 663053
  have htrace : WordTrace (prefixWord ++ tailWord_663053) baseStart_663053 baseEnd_663053 := by
    simpa [prefixWord, tailWord_663053, baseEnd_663053] using wordTrace_append hprefix tailTrace_663053
  have hstable : (prefixWord ++ tailWord_663053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663053).length < 2 ^ (prefixWord ++ tailWord_663053).sum := by decide
  have hdescent : baseEnd_663053 < baseStart_663053 := by decide
  rcases family_descends (prefixWord ++ tailWord_663053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663101 : List Nat := [1, 4, 1, 3, 3, 1, 2, 3, 3]
def baseStart_663101 : Nat := 118140960795 + 663101 * 2 ^ 59
def prefixEnd_663101 : Nat := 4983230072969 + 3 ^ 40 * 663101 * 2
def baseEnd_663101 : Nat := 151328682434273487994649

theorem tailTrace_663101 : CollatzResearch.WordTrace tailWord_663101 prefixEnd_663101 151328682434273487994649 := by
  unfold tailWord_663101
  simp only [CollatzResearch.WordTrace]
  refine ⟨24185280370705800479725157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16123520247137200319816771 24185280370705800479725157)
  ·
    refine ⟨4534740069507337589948467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24185280370705800479725157 4534740069507337589948467)
    ·
      refine ⟨6802110104261006384922701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4534740069507337589948467 6802110104261006384922701)
      ·
        refine ⟨2550791289097877394346013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6802110104261006384922701 2550791289097877394346013)
        ·
          refine ⟨956546733411704022879755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2550791289097877394346013 956546733411704022879755)
          ·
            refine ⟨1434820100117556034319633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956546733411704022879755 1434820100117556034319633)
            ·
              refine ⟨1076115075088167025739725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1434820100117556034319633 1076115075088167025739725)
              ·
                refine ⟨403543153158062634652397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1076115075088167025739725 403543153158062634652397)
                ·
                  refine ⟨151328682434273487994649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403543153158062634652397 151328682434273487994649)
                  ·
                    rfl

theorem cell21_663101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_663101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663101 prefixEnd_663101 := by exact prefixLift 663101
  have htrace : WordTrace (prefixWord ++ tailWord_663101) baseStart_663101 baseEnd_663101 := by
    simpa [prefixWord, tailWord_663101, baseEnd_663101] using wordTrace_append hprefix tailTrace_663101
  have hstable : (prefixWord ++ tailWord_663101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663101).length < 2 ^ (prefixWord ++ tailWord_663101).sum := by decide
  have hdescent : baseEnd_663101 < baseStart_663101 := by decide
  rcases family_descends (prefixWord ++ tailWord_663101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663191 : List Nat := [1, 1, 3, 3, 2, 4, 2, 1, 4]
def baseStart_663191 : Nat := 118140960795 + 663191 * 2 ^ 59
def prefixEnd_663191 : Nat := 4983230072969 + 3 ^ 40 * 663191 * 2
def baseEnd_663191 : Nat := 151349221660453331494465

theorem tailTrace_663191 : CollatzResearch.WordTrace tailWord_663191 prefixEnd_663191 151349221660453331494465 := by
  unfold tailWord_663191
  simp only [CollatzResearch.WordTrace]
  refine ⟨24188562940379745850501427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16125708626919830567000951 24188562940379745850501427)
  ·
    refine ⟨36282844410569618775752141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24188562940379745850501427 36282844410569618775752141)
    ·
      refine ⟨13606066653963607040907053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36282844410569618775752141 13606066653963607040907053)
      ·
        refine ⟨5102274995236352640340145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13606066653963607040907053 5102274995236352640340145)
        ·
          refine ⟨3826706246427264480255109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5102274995236352640340145 3826706246427264480255109)
          ·
            refine ⟨717507421205112090047833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3826706246427264480255109 717507421205112090047833)
            ·
              refine ⟨538130565903834067535875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 717507421205112090047833 538130565903834067535875)
              ·
                refine ⟨807195848855751101303813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538130565903834067535875 807195848855751101303813)
                ·
                  refine ⟨151349221660453331494465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 807195848855751101303813 151349221660453331494465)
                  ·
                    rfl

theorem cell21_663191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 4].length) (baseStart_663191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663191 prefixEnd_663191 := by exact prefixLift 663191
  have htrace : WordTrace (prefixWord ++ tailWord_663191) baseStart_663191 baseEnd_663191 := by
    simpa [prefixWord, tailWord_663191, baseEnd_663191] using wordTrace_append hprefix tailTrace_663191
  have hstable : (prefixWord ++ tailWord_663191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663191).length < 2 ^ (prefixWord ++ tailWord_663191).sum := by decide
  have hdescent : baseEnd_663191 < baseStart_663191 := by decide
  rcases family_descends (prefixWord ++ tailWord_663191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663216 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 8]
def baseStart_663216 : Nat := 118140960795 + 663216 * 2 ^ 59
def prefixEnd_663216 : Nat := 4983230072969 + 3 ^ 40 * 663216 * 2
def baseEnd_663216 : Nat := 151354927001058843577747

theorem tailTrace_663216 : CollatzResearch.WordTrace tailWord_663216 prefixEnd_663216 151354927001058843577747 := by
  unfold tailWord_663216
  simp only [CollatzResearch.WordTrace]
  refine ⟨12094737382644587560080751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16126316510192783413441001 12094737382644587560080751)
  ·
    refine ⟨18142106073966881340121127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12094737382644587560080751 18142106073966881340121127)
    ·
      refine ⟨27213159110950322010181691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18142106073966881340121127 27213159110950322010181691)
      ·
        refine ⟨40819738666425483015272537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27213159110950322010181691 40819738666425483015272537)
        ·
          refine ⟨30614803999819112261454403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40819738666425483015272537 30614803999819112261454403)
          ·
            refine ⟨45922205999728668392181605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30614803999819112261454403 45922205999728668392181605)
            ·
              refine ⟨8610413624949125323534051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45922205999728668392181605 8610413624949125323534051)
              ·
                refine ⟨12915620437423687985301077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8610413624949125323534051 12915620437423687985301077)
                ·
                  refine ⟨151354927001058843577747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12915620437423687985301077 151354927001058843577747)
                  ·
                    rfl

theorem cell21_663216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_663216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663216 prefixEnd_663216 := by exact prefixLift 663216
  have htrace : WordTrace (prefixWord ++ tailWord_663216) baseStart_663216 baseEnd_663216 := by
    simpa [prefixWord, tailWord_663216, baseEnd_663216] using wordTrace_append hprefix tailTrace_663216
  have hstable : (prefixWord ++ tailWord_663216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663216).length < 2 ^ (prefixWord ++ tailWord_663216).sum := by decide
  have hdescent : baseEnd_663216 < baseStart_663216 := by decide
  rcases family_descends (prefixWord ++ tailWord_663216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663219 : List Nat := [1, 1, 1, 2, 3, 3, 2, 5, 3]
def baseStart_663219 : Nat := 118140960795 + 663219 * 2 ^ 59
def prefixEnd_663219 : Nat := 4983230072969 + 3 ^ 40 * 663219 * 2
def baseEnd_663219 : Nat := 151355611641931505027741

theorem tailTrace_663219 : CollatzResearch.WordTrace tailWord_663219 prefixEnd_663219 151355611641931505027741 := by
  unfold tailWord_663219
  simp only [CollatzResearch.WordTrace]
  refine ⟨24189584184278306632520711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16126389456185537755013807 24189584184278306632520711)
  ·
    refine ⟨36284376276417459948781067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24189584184278306632520711 36284376276417459948781067)
    ·
      refine ⟨54426564414626189923171601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36284376276417459948781067 54426564414626189923171601)
      ·
        refine ⟨40819923310969642442378701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54426564414626189923171601 40819923310969642442378701)
        ·
          refine ⟨15307471241613615915892013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40819923310969642442378701 15307471241613615915892013)
          ·
            refine ⟨5740301715605105968459505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15307471241613615915892013 5740301715605105968459505)
            ·
              refine ⟨4305226286703829476344629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5740301715605105968459505 4305226286703829476344629)
              ·
                refine ⟨403614964378484013407309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4305226286703829476344629 403614964378484013407309)
                ·
                  refine ⟨151355611641931505027741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403614964378484013407309 151355611641931505027741)
                  ·
                    rfl

theorem cell21_663219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 3].length) (baseStart_663219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663219 prefixEnd_663219 := by exact prefixLift 663219
  have htrace : WordTrace (prefixWord ++ tailWord_663219) baseStart_663219 baseEnd_663219 := by
    simpa [prefixWord, tailWord_663219, baseEnd_663219] using wordTrace_append hprefix tailTrace_663219
  have hstable : (prefixWord ++ tailWord_663219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663219).length < 2 ^ (prefixWord ++ tailWord_663219).sum := by decide
  have hdescent : baseEnd_663219 < baseStart_663219 := by decide
  rcases family_descends (prefixWord ++ tailWord_663219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663236 : List Nat := [2, 3, 3, 1, 1, 1, 3, 4, 3]
def baseStart_663236 : Nat := 118140960795 + 663236 * 2 ^ 59
def prefixEnd_663236 : Nat := 4983230072969 + 3 ^ 40 * 663236 * 2
def baseEnd_663236 : Nat := 151359491273543253244373

theorem tailTrace_663236 : CollatzResearch.WordTrace tailWord_663236 prefixEnd_663236 151359491273543253244373 := by
  unfold tailWord_663236
  simp only [CollatzResearch.WordTrace]
  refine ⟨12095102112608359267944781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16126802816811145690593041 12095102112608359267944781)
  ·
    refine ⟨4535663292228134725479293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12095102112608359267944781 4535663292228134725479293)
    ·
      refine ⟨1700873734585550522054735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4535663292228134725479293 1700873734585550522054735)
      ·
        refine ⟨2551310601878325783082103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1700873734585550522054735 2551310601878325783082103)
        ·
          refine ⟨3826965902817488674623155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2551310601878325783082103 3826965902817488674623155)
          ·
            refine ⟨5740448854226233011934733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826965902817488674623155 5740448854226233011934733)
            ·
              refine ⟨2152668320334837379475525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5740448854226233011934733 2152668320334837379475525)
              ·
                refine ⟨403625310062782008651661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2152668320334837379475525 403625310062782008651661)
                ·
                  refine ⟨151359491273543253244373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403625310062782008651661 151359491273543253244373)
                  ·
                    rfl

theorem cell21_663236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_663236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663236 prefixEnd_663236 := by exact prefixLift 663236
  have htrace : WordTrace (prefixWord ++ tailWord_663236) baseStart_663236 baseEnd_663236 := by
    simpa [prefixWord, tailWord_663236, baseEnd_663236] using wordTrace_append hprefix tailTrace_663236
  have hstable : (prefixWord ++ tailWord_663236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663236).length < 2 ^ (prefixWord ++ tailWord_663236).sum := by decide
  have hdescent : baseEnd_663236 < baseStart_663236 := by decide
  rcases family_descends (prefixWord ++ tailWord_663236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663250 : List Nat := [3, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_663250 : Nat := 118140960795 + 663250 * 2 ^ 59
def prefixEnd_663250 : Nat := 4983230072969 + 3 ^ 40 * 663250 * 2
def baseEnd_663250 : Nat := 151362686264282340011011

theorem tailTrace_663250 : CollatzResearch.WordTrace tailWord_663250 prefixEnd_663250 151362686264282340011011 := by
  unfold tailWord_663250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6047678711791499731724801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16127143231443999284599469 6047678711791499731724801)
  ·
    refine ⟨4535759033843624798793601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6047678711791499731724801 4535759033843624798793601)
    ·
      refine ⟨3401819275382718599095201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4535759033843624798793601 3401819275382718599095201)
      ·
        refine ⟨2551364456537038949321401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3401819275382718599095201 2551364456537038949321401)
        ·
          refine ⟨1913523342402779211991051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2551364456537038949321401 1913523342402779211991051)
          ·
            refine ⟨2870285013604168817986577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913523342402779211991051 2870285013604168817986577)
            ·
              refine ⟨2152713760203126613489933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2870285013604168817986577 2152713760203126613489933)
              ·
                refine ⟨807267660076172480058725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2152713760203126613489933 807267660076172480058725)
                ·
                  refine ⟨151362686264282340011011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 807267660076172480058725 151362686264282340011011)
                  ·
                    rfl

theorem cell21_663250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_663250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663250 prefixEnd_663250 := by exact prefixLift 663250
  have htrace : WordTrace (prefixWord ++ tailWord_663250) baseStart_663250 baseEnd_663250 := by
    simpa [prefixWord, tailWord_663250, baseEnd_663250] using wordTrace_append hprefix tailTrace_663250
  have hstable : (prefixWord ++ tailWord_663250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663250).length < 2 ^ (prefixWord ++ tailWord_663250).sum := by decide
  have hdescent : baseEnd_663250 < baseStart_663250 := by decide
  rcases family_descends (prefixWord ++ tailWord_663250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663278 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_663278 : Nat := 118140960795 + 663278 * 2 ^ 59
def prefixEnd_663278 : Nat := 4983230072969 + 3 ^ 40 * 663278 * 2
def baseEnd_663278 : Nat := 151369076245760513544287

theorem tailTrace_663278 : CollatzResearch.WordTrace tailWord_663278 prefixEnd_663278 151369076245760513544287 := by
  unfold tailWord_663278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3023967011383069963614811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16127824060709706472612325 3023967011383069963614811)
  ·
    refine ⟨4535950517074604945422217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3023967011383069963614811 4535950517074604945422217)
    ·
      refine ⟨3401962887805953709066663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4535950517074604945422217 3401962887805953709066663)
      ·
        refine ⟨5102944331708930563599995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401962887805953709066663 5102944331708930563599995)
        ·
          refine ⟨7654416497563395845399993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5102944331708930563599995 7654416497563395845399993)
          ·
            refine ⟨5740812373172546884049995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7654416497563395845399993 5740812373172546884049995)
            ·
              refine ⟨8611218559758820326074993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5740812373172546884049995 8611218559758820326074993)
              ·
                refine ⟨6458413919819115244556245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8611218559758820326074993 6458413919819115244556245)
                ·
                  refine ⟨151369076245760513544287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6458413919819115244556245 151369076245760513544287)
                  ·
                    rfl

theorem cell21_663278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_663278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663278 prefixEnd_663278 := by exact prefixLift 663278
  have htrace : WordTrace (prefixWord ++ tailWord_663278) baseStart_663278 baseEnd_663278 := by
    simpa [prefixWord, tailWord_663278, baseEnd_663278] using wordTrace_append hprefix tailTrace_663278
  have hstable : (prefixWord ++ tailWord_663278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663278).length < 2 ^ (prefixWord ++ tailWord_663278).sum := by decide
  have hdescent : baseEnd_663278 < baseStart_663278 := by decide
  rcases family_descends (prefixWord ++ tailWord_663278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663284 : List Nat := [2, 6, 1, 1, 1, 1, 3, 2, 4]
def baseStart_663284 : Nat := 118140960795 + 663284 * 2 ^ 59
def prefixEnd_663284 : Nat := 4983230072969 + 3 ^ 40 * 663284 * 2
def baseEnd_663284 : Nat := 151370445527505836444275

theorem tailTrace_663284 : CollatzResearch.WordTrace tailWord_663284 prefixEnd_663284 151370445527505836444275 := by
  unfold tailWord_663284
  simp only [CollatzResearch.WordTrace]
  refine ⟨12095977464521411366818453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16127969952695215155757937 12095977464521411366818453)
  ·
    refine ⟨566998943649441157819615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12095977464521411366818453 566998943649441157819615)
    ·
      refine ⟨850498415474161736729423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 566998943649441157819615 850498415474161736729423)
      ·
        refine ⟨1275747623211242605094135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850498415474161736729423 1275747623211242605094135)
        ·
          refine ⟨1913621434816863907641203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275747623211242605094135 1913621434816863907641203)
          ·
            refine ⟨2870432152225295861461805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913621434816863907641203 2870432152225295861461805)
            ·
              refine ⟨1076412057084485948048177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2870432152225295861461805 1076412057084485948048177)
              ·
                refine ⟨807309042813364461036133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1076412057084485948048177 807309042813364461036133)
                ·
                  refine ⟨151370445527505836444275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 807309042813364461036133 151370445527505836444275)
                  ·
                    rfl

theorem cell21_663284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_663284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663284 prefixEnd_663284 := by exact prefixLift 663284
  have htrace : WordTrace (prefixWord ++ tailWord_663284) baseStart_663284 baseEnd_663284 := by
    simpa [prefixWord, tailWord_663284, baseEnd_663284] using wordTrace_append hprefix tailTrace_663284
  have hstable : (prefixWord ++ tailWord_663284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663284).length < 2 ^ (prefixWord ++ tailWord_663284).sum := by decide
  have hdescent : baseEnd_663284 < baseStart_663284 := by decide
  rcases family_descends (prefixWord ++ tailWord_663284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663295 : List Nat := [1, 1, 2, 2, 1, 3, 4, 4, 3]
def baseStart_663295 : Nat := 118140960795 + 663295 * 2 ^ 59
def prefixEnd_663295 : Nat := 4983230072969 + 3 ^ 40 * 663295 * 2
def baseEnd_663295 : Nat := 151372955877372261760919

theorem tailTrace_663295 : CollatzResearch.WordTrace tailWord_663295 prefixEnd_663295 151372955877372261760919 := by
  unfold tailWord_663295
  simp only [CollatzResearch.WordTrace]
  refine ⟨24192356132002971612287339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16128237421335314408191559 24192356132002971612287339)
  ·
    refine ⟨36288534198004457418431009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24192356132002971612287339 36288534198004457418431009)
    ·
      refine ⟨27216400648503343063823257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36288534198004457418431009 27216400648503343063823257)
      ·
        refine ⟨20412300486377507297867443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27216400648503343063823257 20412300486377507297867443)
        ·
          refine ⟨30618450729566260946801165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20412300486377507297867443 30618450729566260946801165)
          ·
            refine ⟨11481919023587347855050437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30618450729566260946801165 11481919023587347855050437)
            ·
              refine ⟨2152859816922627722821957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11481919023587347855050437 2152859816922627722821957)
              ·
                refine ⟨403661215672992698029117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2152859816922627722821957 403661215672992698029117)
                ·
                  refine ⟨151372955877372261760919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403661215672992698029117 151372955877372261760919)
                  ·
                    rfl

theorem cell21_663295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 3].length) (baseStart_663295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663295 prefixEnd_663295 := by exact prefixLift 663295
  have htrace : WordTrace (prefixWord ++ tailWord_663295) baseStart_663295 baseEnd_663295 := by
    simpa [prefixWord, tailWord_663295, baseEnd_663295] using wordTrace_append hprefix tailTrace_663295
  have hstable : (prefixWord ++ tailWord_663295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663295).length < 2 ^ (prefixWord ++ tailWord_663295).sum := by decide
  have hdescent : baseEnd_663295 < baseStart_663295 := by decide
  rcases family_descends (prefixWord ++ tailWord_663295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663447 : List Nat := [1, 1, 3, 3, 1, 3, 1, 5, 3]
def baseStart_663447 : Nat := 118140960795 + 663447 * 2 ^ 59
def prefixEnd_663447 : Nat := 4983230072969 + 3 ^ 40 * 663447 * 2
def baseEnd_663447 : Nat := 151407644348253775227275

theorem tailTrace_663447 : CollatzResearch.WordTrace tailWord_663447 prefixEnd_663447 151407644348253775227275 := by
  unfold tailWord_663447
  simp only [CollatzResearch.WordTrace]
  refine ⟨24197900027452301571820595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16131933351634867714547063 24197900027452301571820595)
  ·
    refine ⟨36296850041178452357730893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24197900027452301571820595 36296850041178452357730893)
    ·
      refine ⟨13611318765441919634149085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36296850041178452357730893 13611318765441919634149085)
      ·
        refine ⟨5104244537040719862805907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13611318765441919634149085 5104244537040719862805907)
        ·
          refine ⟨7656366805561079794208861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5104244537040719862805907 7656366805561079794208861)
          ·
            refine ⟨2871137552085404922828323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7656366805561079794208861 2871137552085404922828323)
            ·
              refine ⟨4306706328128107384242485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871137552085404922828323 4306706328128107384242485)
              ·
                refine ⟨403753718262010067272733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4306706328128107384242485 403753718262010067272733)
                ·
                  refine ⟨151407644348253775227275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403753718262010067272733 151407644348253775227275)
                  ·
                    rfl

theorem cell21_663447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 3].length) (baseStart_663447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663447 prefixEnd_663447 := by exact prefixLift 663447
  have htrace : WordTrace (prefixWord ++ tailWord_663447) baseStart_663447 baseEnd_663447 := by
    simpa [prefixWord, tailWord_663447, baseEnd_663447] using wordTrace_append hprefix tailTrace_663447
  have hstable : (prefixWord ++ tailWord_663447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663447).length < 2 ^ (prefixWord ++ tailWord_663447).sum := by decide
  have hdescent : baseEnd_663447 < baseStart_663447 := by decide
  rcases family_descends (prefixWord ++ tailWord_663447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663523 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 5]
def baseStart_663523 : Nat := 118140960795 + 663523 * 2 ^ 59
def prefixEnd_663523 : Nat := 4983230072969 + 3 ^ 40 * 663523 * 2
def baseEnd_663523 : Nat := 151424988583694531960453

theorem tailTrace_663523 : CollatzResearch.WordTrace tailWord_663523 prefixEnd_663523 151424988583694531960453 := by
  unfold tailWord_663523
  simp only [CollatzResearch.WordTrace]
  refine ⟨24200671975176966551587223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16133781316784644367724815 24200671975176966551587223)
  ·
    refine ⟨36301007962765449827380835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24200671975176966551587223 36301007962765449827380835)
    ·
      refine ⟨54451511944148174741071253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36301007962765449827380835 54451511944148174741071253)
      ·
        refine ⟨2552414622381945690987715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54451511944148174741071253 2552414622381945690987715)
        ·
          refine ⟨3828621933572918536481573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552414622381945690987715 3828621933572918536481573)
          ·
            refine ⟨717866612544922225590295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3828621933572918536481573 717866612544922225590295)
            ·
              refine ⟨1076799918817383338385443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717866612544922225590295 1076799918817383338385443)
              ·
                refine ⟨1615199878226075007578165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076799918817383338385443 1615199878226075007578165)
                ·
                  refine ⟨151424988583694531960453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1615199878226075007578165 151424988583694531960453)
                  ·
                    rfl

theorem cell21_663523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 5].length) (baseStart_663523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663523 prefixEnd_663523 := by exact prefixLift 663523
  have htrace : WordTrace (prefixWord ++ tailWord_663523) baseStart_663523 baseEnd_663523 := by
    simpa [prefixWord, tailWord_663523, baseEnd_663523] using wordTrace_append hprefix tailTrace_663523
  have hstable : (prefixWord ++ tailWord_663523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663523).length < 2 ^ (prefixWord ++ tailWord_663523).sum := by decide
  have hdescent : baseEnd_663523 < baseStart_663523 := by decide
  rcases family_descends (prefixWord ++ tailWord_663523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663585 : List Nat := [1, 2, 3, 2, 5, 1, 1, 6]
def baseStart_663585 : Nat := 118140960795 + 663585 * 2 ^ 59
def prefixEnd_663585 : Nat := 4983230072969 + 3 ^ 40 * 663585 * 2
def baseEnd_663585 : Nat := 50479712609465400642331

theorem tailTrace_663585 : CollatzResearch.WordTrace tailWord_663585 prefixEnd_663585 50479712609465400642331 := by
  unfold tailWord_663585
  simp only [CollatzResearch.WordTrace]
  refine ⟨24202933300952351140344209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16135288867301567426896139 24202933300952351140344209)
  ·
    refine ⟨18152199975714263355258157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24202933300952351140344209 18152199975714263355258157)
    ·
      refine ⟨6807074990892848758221809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18152199975714263355258157 6807074990892848758221809)
      ·
        refine ⟨5105306243169636568666357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6807074990892848758221809 5105306243169636568666357)
        ·
          refine ⟨478622460297153428312471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5105306243169636568666357 478622460297153428312471)
          ·
            refine ⟨717933690445730142468707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478622460297153428312471 717933690445730142468707)
            ·
              refine ⟨1076900535668595213703061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717933690445730142468707 1076900535668595213703061)
              ·
                refine ⟨50479712609465400642331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1076900535668595213703061 50479712609465400642331)
                ·
                  rfl

theorem cell21_663585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 6].length) (baseStart_663585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663585 prefixEnd_663585 := by exact prefixLift 663585
  have htrace : WordTrace (prefixWord ++ tailWord_663585) baseStart_663585 baseEnd_663585 := by
    simpa [prefixWord, tailWord_663585, baseEnd_663585] using wordTrace_append hprefix tailTrace_663585
  have hstable : (prefixWord ++ tailWord_663585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663585).length < 2 ^ (prefixWord ++ tailWord_663585).sum := by decide
  have hdescent : baseEnd_663585 < baseStart_663585 := by decide
  rcases family_descends (prefixWord ++ tailWord_663585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663630 : List Nat := [4, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_663630 : Nat := 118140960795 + 663630 * 2 ^ 59
def prefixEnd_663630 : Nat := 4983230072969 + 3 ^ 40 * 663630 * 2
def baseEnd_663630 : Nat := 151449407441486123676901

theorem tailTrace_663630 : CollatzResearch.WordTrace tailWord_663630 prefixEnd_663630 151449407441486123676901 := by
  unfold tailWord_663630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3025571823223665478216543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16136383057192882550488229 3025571823223665478216543)
  ·
    refine ⟨4538357734835498217324815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3025571823223665478216543 4538357734835498217324815)
    ·
      refine ⟨6807536602253247325987223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4538357734835498217324815 6807536602253247325987223)
      ·
        refine ⟨10211304903379870988980835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6807536602253247325987223 10211304903379870988980835)
        ·
          refine ⟨15316957355069806483471253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10211304903379870988980835 15316957355069806483471253)
          ·
            refine ⟨717982376018897178912715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15316957355069806483471253 717982376018897178912715)
            ·
              refine ⟨1076973564028345768369073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717982376018897178912715 1076973564028345768369073)
              ·
                refine ⟨807730173021259326276805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1076973564028345768369073 807730173021259326276805)
                ·
                  refine ⟨151449407441486123676901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 807730173021259326276805 151449407441486123676901)
                  ·
                    rfl

theorem cell21_663630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_663630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663630 prefixEnd_663630 := by exact prefixLift 663630
  have htrace : WordTrace (prefixWord ++ tailWord_663630) baseStart_663630 baseEnd_663630 := by
    simpa [prefixWord, tailWord_663630, baseEnd_663630] using wordTrace_append hprefix tailTrace_663630
  have hstable : (prefixWord ++ tailWord_663630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663630).length < 2 ^ (prefixWord ++ tailWord_663630).sum := by decide
  have hdescent : baseEnd_663630 < baseStart_663630 := by decide
  rcases family_descends (prefixWord ++ tailWord_663630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663706 : List Nat := [3, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_663706 : Nat := 118140960795 + 663706 * 2 ^ 59
def prefixEnd_663706 : Nat := 4983230072969 + 3 ^ 40 * 663706 * 2
def baseEnd_663706 : Nat := 151466751676926880410079

theorem tailTrace_663706 : CollatzResearch.WordTrace tailWord_663706 prefixEnd_663706 151466751676926880410079 := by
  unfold tailWord_663706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6051836633378497201374743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16138231022342659203665981 6051836633378497201374743)
  ·
    refine ⟨9077754950067745802062115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6051836633378497201374743 9077754950067745802062115)
    ·
      refine ⟨13616632425101618703093173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9077754950067745802062115 13616632425101618703093173)
      ·
        refine ⟨1276559289853276753414985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13616632425101618703093173 1276559289853276753414985)
        ·
          refine ⟨957419467389957565061239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1276559289853276753414985 957419467389957565061239)
          ·
            refine ⟨1436129201084936347591859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957419467389957565061239 1436129201084936347591859)
            ·
              refine ⟨2154193801627404521387789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436129201084936347591859 2154193801627404521387789)
              ·
                refine ⟨807822675610276695520421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2154193801627404521387789 807822675610276695520421)
                ·
                  refine ⟨151466751676926880410079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 807822675610276695520421 151466751676926880410079)
                  ·
                    rfl

theorem cell21_663706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_663706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663706 prefixEnd_663706 := by exact prefixLift 663706
  have htrace : WordTrace (prefixWord ++ tailWord_663706) baseStart_663706 baseEnd_663706 := by
    simpa [prefixWord, tailWord_663706, baseEnd_663706] using wordTrace_append hprefix tailTrace_663706
  have hstable : (prefixWord ++ tailWord_663706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663706).length < 2 ^ (prefixWord ++ tailWord_663706).sum := by decide
  have hdescent : baseEnd_663706 < baseStart_663706 := by decide
  rcases family_descends (prefixWord ++ tailWord_663706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663717 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 7]
def baseStart_663717 : Nat := 118140960795 + 663717 * 2 ^ 59
def prefixEnd_663717 : Nat := 4983230072969 + 3 ^ 40 * 663717 * 2
def baseEnd_663717 : Nat := 151469262026793305726723

theorem tailTrace_663717 : CollatzResearch.WordTrace tailWord_663717 prefixEnd_663717 151469262026793305726723 := by
  unfold tailWord_663717
  simp only [CollatzResearch.WordTrace]
  refine ⟨24207747736474137684149405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16138498490982758456099603 24207747736474137684149405)
  ·
    refine ⟨9077905401177801631556027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24207747736474137684149405 9077905401177801631556027)
    ·
      refine ⟨13616858101766702447334041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9077905401177801631556027 13616858101766702447334041)
      ·
        refine ⟨10212643576325026835500531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13616858101766702447334041 10212643576325026835500531)
        ·
          refine ⟨15318965364487540253250797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10212643576325026835500531 15318965364487540253250797)
          ·
            refine ⟨5744612011682827594969049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15318965364487540253250797 5744612011682827594969049)
            ·
              refine ⟨4308459008762120696226787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5744612011682827594969049 4308459008762120696226787)
              ·
                refine ⟨6462688513143181044340181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4308459008762120696226787 6462688513143181044340181)
                ·
                  refine ⟨151469262026793305726723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6462688513143181044340181 151469262026793305726723)
                  ·
                    rfl

theorem cell21_663717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_663717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663717 prefixEnd_663717 := by exact prefixLift 663717
  have htrace : WordTrace (prefixWord ++ tailWord_663717) baseStart_663717 baseEnd_663717 := by
    simpa [prefixWord, tailWord_663717, baseEnd_663717] using wordTrace_append hprefix tailTrace_663717
  have hstable : (prefixWord ++ tailWord_663717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663717).length < 2 ^ (prefixWord ++ tailWord_663717).sum := by decide
  have hdescent : baseEnd_663717 < baseStart_663717 := by decide
  rcases family_descends (prefixWord ++ tailWord_663717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663844 : List Nat := [2, 3, 1, 3, 1, 4, 1, 3, 3]
def baseStart_663844 : Nat := 118140960795 + 663844 * 2 ^ 59
def prefixEnd_663844 : Nat := 4983230072969 + 3 ^ 40 * 663844 * 2
def baseEnd_663844 : Nat := 151498245157069307109797

theorem tailTrace_663844 : CollatzResearch.WordTrace tailWord_663844 prefixEnd_663844 151498245157069307109797 := by
  unfold tailWord_663844
  simp only [CollatzResearch.WordTrace]
  refine ⟨12106189903507019187011293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16141586538009358916015057 12106189903507019187011293)
  ·
    refine ⟨4539821213815132195129235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12106189903507019187011293 4539821213815132195129235)
    ·
      refine ⟨6809731820722698292693853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4539821213815132195129235 6809731820722698292693853)
      ·
        refine ⟨2553649432771011859760195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6809731820722698292693853 2553649432771011859760195)
        ·
          refine ⟨3830474149156517789640293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2553649432771011859760195 3830474149156517789640293)
          ·
            refine ⟨718213902966847085557555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3830474149156517789640293 718213902966847085557555)
            ·
              refine ⟨1077320854450270628336333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718213902966847085557555 1077320854450270628336333)
              ·
                refine ⟨403995320418851485626125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1077320854450270628336333 403995320418851485626125)
                ·
                  refine ⟨151498245157069307109797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403995320418851485626125 151498245157069307109797)
                  ·
                    rfl

theorem cell21_663844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_663844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663844 prefixEnd_663844 := by exact prefixLift 663844
  have htrace : WordTrace (prefixWord ++ tailWord_663844) baseStart_663844 baseEnd_663844 := by
    simpa [prefixWord, tailWord_663844, baseEnd_663844] using wordTrace_append hprefix tailTrace_663844
  have hstable : (prefixWord ++ tailWord_663844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663844).length < 2 ^ (prefixWord ++ tailWord_663844).sum := by decide
  have hdescent : baseEnd_663844 < baseStart_663844 := by decide
  rcases family_descends (prefixWord ++ tailWord_663844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663883 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 8]
def baseStart_663883 : Nat := 118140960795 + 663883 * 2 ^ 59
def prefixEnd_663883 : Nat := 4983230072969 + 3 ^ 40 * 663883 * 2
def baseEnd_663883 : Nat := 151507145488413905959717

theorem tailTrace_663883 : CollatzResearch.WordTrace tailWord_663883 prefixEnd_663883 151507145488413905959717 := by
  unfold tailWord_663883
  simp only [CollatzResearch.WordTrace]
  refine ⟨24213802253872748034692303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16142534835915165356461535 24213802253872748034692303)
  ·
    refine ⟨36320703380809122052038455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24213802253872748034692303 36320703380809122052038455)
    ·
      refine ⟨54481055071213683078057683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36320703380809122052038455 54481055071213683078057683)
      ·
        refine ⟨81721582606820524617086525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54481055071213683078057683 81721582606820524617086525)
        ·
          refine ⟨30645593477557696731407447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81721582606820524617086525 30645593477557696731407447)
          ·
            refine ⟨45968390216336545097111171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30645593477557696731407447 45968390216336545097111171)
            ·
              refine ⟨68952585324504817645666757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45968390216336545097111171 68952585324504817645666757)
              ·
                refine ⟨12928609748344653308562517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68952585324504817645666757 12928609748344653308562517)
                ·
                  refine ⟨151507145488413905959717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12928609748344653308562517 151507145488413905959717)
                  ·
                    rfl

theorem cell21_663883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_663883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663883 prefixEnd_663883 := by exact prefixLift 663883
  have htrace : WordTrace (prefixWord ++ tailWord_663883) baseStart_663883 baseEnd_663883 := by
    simpa [prefixWord, tailWord_663883, baseEnd_663883] using wordTrace_append hprefix tailTrace_663883
  have hstable : (prefixWord ++ tailWord_663883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663883).length < 2 ^ (prefixWord ++ tailWord_663883).sum := by decide
  have hdescent : baseEnd_663883 < baseStart_663883 := by decide
  rcases family_descends (prefixWord ++ tailWord_663883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663917 : List Nat := [1, 5, 1, 1, 1, 2, 4, 2, 4]
def baseStart_663917 : Nat := 118140960795 + 663917 * 2 ^ 59
def prefixEnd_663917 : Nat := 4983230072969 + 3 ^ 40 * 663917 * 2
def baseEnd_663917 : Nat := 151514904751637402392981

theorem tailTrace_663917 : CollatzResearch.WordTrace tailWord_663917 prefixEnd_663917 151514904751637402392981 := by
  unfold tailWord_663917
  simp only [CollatzResearch.WordTrace]
  refine ⟨24215042335749571841430005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16143361557166381227620003 24215042335749571841430005)
  ·
    refine ⟨2270160218976522360134063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24215042335749571841430005 2270160218976522360134063)
    ·
      refine ⟨3405240328464783540201095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2270160218976522360134063 3405240328464783540201095)
      ·
        refine ⟨5107860492697175310301643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3405240328464783540201095 5107860492697175310301643)
        ·
          refine ⟨7661790739045762965452465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5107860492697175310301643 7661790739045762965452465)
          ·
            refine ⟨5746343054284322224089349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7661790739045762965452465 5746343054284322224089349)
            ·
              refine ⟨1077439322678310417016753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5746343054284322224089349 1077439322678310417016753)
              ·
                refine ⟨808079492008732812762565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077439322678310417016753 808079492008732812762565)
                ·
                  refine ⟨151514904751637402392981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 808079492008732812762565 151514904751637402392981)
                  ·
                    rfl

theorem cell21_663917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_663917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663917 prefixEnd_663917 := by exact prefixLift 663917
  have htrace : WordTrace (prefixWord ++ tailWord_663917) baseStart_663917 baseEnd_663917 := by
    simpa [prefixWord, tailWord_663917, baseEnd_663917] using wordTrace_append hprefix tailTrace_663917
  have hstable : (prefixWord ++ tailWord_663917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663917).length < 2 ^ (prefixWord ++ tailWord_663917).sum := by decide
  have hdescent : baseEnd_663917 < baseStart_663917 := by decide
  rcases family_descends (prefixWord ++ tailWord_663917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663920 : List Nat := [2, 1, 1, 1, 4, 5, 2, 2, 3]
def baseStart_663920 : Nat := 118140960795 + 663920 * 2 ^ 59
def prefixEnd_663920 : Nat := 4983230072969 + 3 ^ 40 * 663920 * 2
def baseEnd_663920 : Nat := 151515589392510063842975

theorem tailTrace_663920 : CollatzResearch.WordTrace tailWord_663920 prefixEnd_663920 151515589392510063842975 := by
  unfold tailWord_663920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12107575877369351676894607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16143434503159135569192809 12107575877369351676894607)
  ·
    refine ⟨18161363816054027515341911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12107575877369351676894607 18161363816054027515341911)
    ·
      refine ⟨27242045724081041273012867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18161363816054027515341911 27242045724081041273012867)
      ·
        refine ⟨40863068586121561909519301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27242045724081041273012867 40863068586121561909519301)
        ·
          refine ⟨7661825359897792858034869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40863068586121561909519301 7661825359897792858034869)
          ·
            refine ⟨718296127490418080440769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7661825359897792858034869 718296127490418080440769)
            ·
              refine ⟨538722095617813560330577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718296127490418080440769 538722095617813560330577)
              ·
                refine ⟨404041571713360170247933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538722095617813560330577 404041571713360170247933)
                ·
                  refine ⟨151515589392510063842975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404041571713360170247933 151515589392510063842975)
                  ·
                    rfl

theorem cell21_663920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 3].length) (baseStart_663920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663920 prefixEnd_663920 := by exact prefixLift 663920
  have htrace : WordTrace (prefixWord ++ tailWord_663920) baseStart_663920 baseEnd_663920 := by
    simpa [prefixWord, tailWord_663920, baseEnd_663920] using wordTrace_append hprefix tailTrace_663920
  have hstable : (prefixWord ++ tailWord_663920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663920).length < 2 ^ (prefixWord ++ tailWord_663920).sum := by decide
  have hdescent : baseEnd_663920 < baseStart_663920 := by decide
  rcases family_descends (prefixWord ++ tailWord_663920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663931 : List Nat := [1, 1, 1, 1, 1, 9, 1, 6]
def baseStart_663931 : Nat := 118140960795 + 663931 * 2 ^ 59
def prefixEnd_663931 : Nat := 4983230072969 + 3 ^ 40 * 663931 * 2
def baseEnd_663931 : Nat := 50506033247458829719873

theorem tailTrace_663931 : CollatzResearch.WordTrace tailWord_663931 prefixEnd_663931 50506033247458829719873 := by
  unfold tailWord_663931
  simp only [CollatzResearch.WordTrace]
  refine ⟨24215552957698852232439647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16143701971799234821626431 24215552957698852232439647)
  ·
    refine ⟨36323329436548278348659471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24215552957698852232439647 36323329436548278348659471)
    ·
      refine ⟨54484994154822417522989207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36323329436548278348659471 54484994154822417522989207)
      ·
        refine ⟨81727491232233626284483811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54484994154822417522989207 81727491232233626284483811)
        ·
          refine ⟨122591236848350439426725717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81727491232233626284483811 122591236848350439426725717)
          ·
            refine ⟨718308028408303356015971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 122591236848350439426725717 718308028408303356015971)
            ·
              refine ⟨1077462042612455034023957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718308028408303356015971 1077462042612455034023957)
              ·
                refine ⟨50506033247458829719873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1077462042612455034023957 50506033247458829719873)
                ·
                  rfl

theorem cell21_663931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 6].length) (baseStart_663931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663931 prefixEnd_663931 := by exact prefixLift 663931
  have htrace : WordTrace (prefixWord ++ tailWord_663931) baseStart_663931 baseEnd_663931 := by
    simpa [prefixWord, tailWord_663931, baseEnd_663931] using wordTrace_append hprefix tailTrace_663931
  have hstable : (prefixWord ++ tailWord_663931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663931).length < 2 ^ (prefixWord ++ tailWord_663931).sum := by decide
  have hdescent : baseEnd_663931 < baseStart_663931 := by decide
  rcases family_descends (prefixWord ++ tailWord_663931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663945 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 7]
def baseStart_663945 : Nat := 118140960795 + 663945 * 2 ^ 59
def prefixEnd_663945 : Nat := 4983230072969 + 3 ^ 40 * 663945 * 2
def baseEnd_663945 : Nat := 151521294733115575926257

theorem tailTrace_663945 : CollatzResearch.WordTrace tailWord_663945 prefixEnd_663945 151521294733115575926257 := by
  unfold tailWord_663945
  simp only [CollatzResearch.WordTrace]
  refine ⟨24216063579648132623449289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16144042386432088415632859 24216063579648132623449289)
  ·
    refine ⟨18162047684736099467586967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24216063579648132623449289 18162047684736099467586967)
    ·
      refine ⟨27243071527104149201380451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18162047684736099467586967 27243071527104149201380451)
      ·
        refine ⟨40864607290656223802070677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27243071527104149201380451 40864607290656223802070677)
        ·
          refine ⟨1915528466749510490722063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40864607290656223802070677 1915528466749510490722063)
          ·
            refine ⟨2873292700124265736083095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915528466749510490722063 2873292700124265736083095)
            ·
              refine ⟨4309939050186398604124643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873292700124265736083095 4309939050186398604124643)
              ·
                refine ⟨6464908575279597906186965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4309939050186398604124643 6464908575279597906186965)
                ·
                  refine ⟨151521294733115575926257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6464908575279597906186965 151521294733115575926257)
                  ·
                    rfl

theorem cell21_663945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_663945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_663945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_663945 prefixEnd_663945 := by exact prefixLift 663945
  have htrace : WordTrace (prefixWord ++ tailWord_663945) baseStart_663945 baseEnd_663945 := by
    simpa [prefixWord, tailWord_663945, baseEnd_663945] using wordTrace_append hprefix tailTrace_663945
  have hstable : (prefixWord ++ tailWord_663945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663945).length < 2 ^ (prefixWord ++ tailWord_663945).sum := by decide
  have hdescent : baseEnd_663945 < baseStart_663945 := by decide
  rcases family_descends (prefixWord ++ tailWord_663945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664007 : List Nat := [1, 1, 4, 1, 1, 4, 4, 5]
def baseStart_664007 : Nat := 118140960795 + 664007 * 2 ^ 59
def prefixEnd_664007 : Nat := 4983230072969 + 3 ^ 40 * 664007 * 2
def baseEnd_664007 : Nat := 50511814659272415297599

theorem tailTrace_664007 : CollatzResearch.WordTrace tailWord_664007 prefixEnd_664007 50511814659272415297599 := by
  unfold tailWord_664007
  simp only [CollatzResearch.WordTrace]
  refine ⟨24218324905423517212206275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16145549936949011474804183 24218324905423517212206275)
  ·
    refine ⟨36327487358135275818309413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24218324905423517212206275 36327487358135275818309413)
    ·
      refine ⟨6811403879650364215933015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36327487358135275818309413 6811403879650364215933015)
      ·
        refine ⟨10217105819475546323899523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6811403879650364215933015 10217105819475546323899523)
        ·
          refine ⟨15325658729213319485849285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10217105819475546323899523 15325658729213319485849285)
          ·
            refine ⟨2873561011727497403596741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15325658729213319485849285 2873561011727497403596741)
            ·
              refine ⟨538792689698905763174389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2873561011727497403596741 538792689698905763174389)
              ·
                refine ⟨50511814659272415297599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 538792689698905763174389 50511814659272415297599)
                ·
                  rfl

theorem cell21_664007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 5].length) (baseStart_664007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664007 prefixEnd_664007 := by exact prefixLift 664007
  have htrace : WordTrace (prefixWord ++ tailWord_664007) baseStart_664007 baseEnd_664007 := by
    simpa [prefixWord, tailWord_664007, baseEnd_664007] using wordTrace_append hprefix tailTrace_664007
  have hstable : (prefixWord ++ tailWord_664007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664007).length < 2 ^ (prefixWord ++ tailWord_664007).sum := by decide
  have hdescent : baseEnd_664007 < baseStart_664007 := by decide
  rcases family_descends (prefixWord ++ tailWord_664007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664097 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 5]
def baseStart_664097 : Nat := 118140960795 + 664097 * 2 ^ 59
def prefixEnd_664097 : Nat := 4983230072969 + 3 ^ 40 * 664097 * 2
def baseEnd_664097 : Nat := 151555983203997089392613

theorem tailTrace_664097 : CollatzResearch.WordTrace tailWord_664097 prefixEnd_664097 151555983203997089392613 := by
  unfold tailWord_664097
  simp only [CollatzResearch.WordTrace]
  refine ⟨24221607475097462582982545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16147738316731641721988363 24221607475097462582982545)
  ·
    refine ⟨18166205606323096937236909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24221607475097462582982545 18166205606323096937236909)
    ·
      refine ⟨6812327102371161351463841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18166205606323096937236909 6812327102371161351463841)
      ·
        refine ⟨5109245326778371013597881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6812327102371161351463841 5109245326778371013597881)
        ·
          refine ⟨3831933995083778260198411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5109245326778371013597881 3831933995083778260198411)
          ·
            refine ⟨5747900992625667390297617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831933995083778260198411 5747900992625667390297617)
            ·
              refine ⟨4310925744469250542723213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5747900992625667390297617 4310925744469250542723213)
              ·
                refine ⟨1616597154175968953521205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4310925744469250542723213 1616597154175968953521205)
                ·
                  refine ⟨151555983203997089392613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1616597154175968953521205 151555983203997089392613)
                  ·
                    rfl

theorem cell21_664097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_664097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664097 prefixEnd_664097 := by exact prefixLift 664097
  have htrace : WordTrace (prefixWord ++ tailWord_664097) baseStart_664097 baseEnd_664097 := by
    simpa [prefixWord, tailWord_664097, baseEnd_664097] using wordTrace_append hprefix tailTrace_664097
  have hstable : (prefixWord ++ tailWord_664097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664097).length < 2 ^ (prefixWord ++ tailWord_664097).sum := by decide
  have hdescent : baseEnd_664097 < baseStart_664097 := by decide
  rcases family_descends (prefixWord ++ tailWord_664097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664145 : List Nat := [1, 2, 2, 1, 3, 5, 1, 2, 4]
def baseStart_664145 : Nat := 118140960795 + 664145 * 2 ^ 59
def prefixEnd_664145 : Nat := 4983230072969 + 3 ^ 40 * 664145 * 2
def baseEnd_664145 : Nat := 151566937457959672592515

theorem tailTrace_664145 : CollatzResearch.WordTrace tailWord_664145 prefixEnd_664145 151566937457959672592515 := by
  unfold tailWord_664145
  simp only [CollatzResearch.WordTrace]
  refine ⟨24223358178923566780729889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16148905452615711187153259 24223358178923566780729889)
  ·
    refine ⟨18167518634192675085547417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24223358178923566780729889 18167518634192675085547417)
    ·
      refine ⟨13625638975644506314160563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18167518634192675085547417 13625638975644506314160563)
      ·
        refine ⟨20438458463466759471240845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13625638975644506314160563 20438458463466759471240845)
        ·
          refine ⟨7664421923800034801715317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20438458463466759471240845 7664421923800034801715317)
          ·
            refine ⟨718539555356253262660811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7664421923800034801715317 718539555356253262660811)
            ·
              refine ⟨1077809333034379893991217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718539555356253262660811 1077809333034379893991217)
              ·
                refine ⟨808356999775784920493413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077809333034379893991217 808356999775784920493413)
                ·
                  refine ⟨151566937457959672592515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 808356999775784920493413 151566937457959672592515)
                  ·
                    rfl

theorem cell21_664145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_664145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664145 prefixEnd_664145 := by exact prefixLift 664145
  have htrace : WordTrace (prefixWord ++ tailWord_664145) baseStart_664145 baseEnd_664145 := by
    simpa [prefixWord, tailWord_664145, baseEnd_664145] using wordTrace_append hprefix tailTrace_664145
  have hstable : (prefixWord ++ tailWord_664145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664145).length < 2 ^ (prefixWord ++ tailWord_664145).sum := by decide
  have hdescent : baseEnd_664145 < baseStart_664145 := by decide
  rcases family_descends (prefixWord ++ tailWord_664145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664176 : List Nat := [2, 1, 1, 1, 7, 2, 2, 5]
def baseStart_664176 : Nat := 118140960795 + 664176 * 2 ^ 59
def prefixEnd_664176 : Nat := 4983230072969 + 3 ^ 40 * 664176 * 2
def baseEnd_664176 : Nat := 50524670693436835858595

theorem tailTrace_664176 : CollatzResearch.WordTrace tailWord_664176 prefixEnd_664176 50524670693436835858595 := by
  unfold tailWord_664176
  simp only [CollatzResearch.WordTrace]
  refine ⟨12112244420905629537554191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16149659227874172716738921 12112244420905629537554191)
  ·
    refine ⟨18168366631358444306331287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12112244420905629537554191 18168366631358444306331287)
    ·
      refine ⟨27252549947037666459496931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18168366631358444306331287 27252549947037666459496931)
      ·
        refine ⟨40878824920556499689245397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27252549947037666459496931 40878824920556499689245397)
        ·
          refine ⟨958097459075542961466689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 40878824920556499689245397 958097459075542961466689)
          ·
            refine ⟨718573094306657221100017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 958097459075542961466689 718573094306657221100017)
            ·
              refine ⟨538929820729992915825013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718573094306657221100017 538929820729992915825013)
              ·
                refine ⟨50524670693436835858595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 538929820729992915825013 50524670693436835858595)
                ·
                  rfl

theorem cell21_664176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 5].length) (baseStart_664176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664176 prefixEnd_664176 := by exact prefixLift 664176
  have htrace : WordTrace (prefixWord ++ tailWord_664176) baseStart_664176 baseEnd_664176 := by
    simpa [prefixWord, tailWord_664176, baseEnd_664176] using wordTrace_append hprefix tailTrace_664176
  have hstable : (prefixWord ++ tailWord_664176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664176).length < 2 ^ (prefixWord ++ tailWord_664176).sum := by decide
  have hdescent : baseEnd_664176 < baseStart_664176 := by decide
  rcases family_descends (prefixWord ++ tailWord_664176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664221 : List Nat := [1, 4, 2, 1, 1, 1, 6, 1, 4]
def baseStart_664221 : Nat := 118140960795 + 664221 * 2 ^ 59
def prefixEnd_664221 : Nat := 4983230072969 + 3 ^ 40 * 664221 * 2
def baseEnd_664221 : Nat := 151584281693400429325693

theorem tailTrace_664221 : CollatzResearch.WordTrace tailWord_664221 prefixEnd_664221 151584281693400429325693 := by
  unfold tailWord_664221
  simp only [CollatzResearch.WordTrace]
  refine ⟨24226130126648231760496517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16150753417765487840331011 24226130126648231760496517)
  ·
    refine ⟨4542399398746543455093097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24226130126648231760496517 4542399398746543455093097)
    ·
      refine ⟨3406799549059907591319823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4542399398746543455093097 3406799549059907591319823)
      ·
        refine ⟨5110199323589861386979735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3406799549059907591319823 5110199323589861386979735)
        ·
          refine ⟨7665298985384792080469603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5110199323589861386979735 7665298985384792080469603)
          ·
            refine ⟨11497948478077188120704405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7665298985384792080469603 11497948478077188120704405)
            ·
              refine ⟨538966334909868193158019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11497948478077188120704405 538966334909868193158019)
              ·
                refine ⟨808449502364802289737029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538966334909868193158019 808449502364802289737029)
                ·
                  refine ⟨151584281693400429325693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 808449502364802289737029 151584281693400429325693)
                  ·
                    rfl

theorem cell21_664221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_664221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664221 prefixEnd_664221 := by exact prefixLift 664221
  have htrace : WordTrace (prefixWord ++ tailWord_664221) baseStart_664221 baseEnd_664221 := by
    simpa [prefixWord, tailWord_664221, baseEnd_664221] using wordTrace_append hprefix tailTrace_664221
  have hstable : (prefixWord ++ tailWord_664221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664221).length < 2 ^ (prefixWord ++ tailWord_664221).sum := by decide
  have hdescent : baseEnd_664221 < baseStart_664221 := by decide
  rcases family_descends (prefixWord ++ tailWord_664221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664269 : List Nat := [1, 6, 2, 1, 2, 2, 1, 6]
def baseStart_664269 : Nat := 118140960795 + 664269 * 2 ^ 59
def prefixEnd_664269 : Nat := 4983230072969 + 3 ^ 40 * 664269 * 2
def baseEnd_664269 : Nat := 50531745315787670841865

theorem tailTrace_664269 : CollatzResearch.WordTrace tailWord_664269 prefixEnd_664269 50531745315787670841865 := by
  unfold tailWord_664269
  simp only [CollatzResearch.WordTrace]
  refine ⟨24227880830474335958243861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16151920553649557305495907 24227880830474335958243861)
  ·
    refine ⟨1135681913928484498042681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24227880830474335958243861 1135681913928484498042681)
    ·
      refine ⟨851761435446363373532011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1135681913928484498042681 851761435446363373532011)
      ·
        refine ⟨1277642153169545060298017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851761435446363373532011 1277642153169545060298017)
        ·
          refine ⟨958231614877158795223513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1277642153169545060298017 958231614877158795223513)
          ·
            refine ⟨718673711157869096417635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 958231614877158795223513 718673711157869096417635)
            ·
              refine ⟨1078010566736803644626453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718673711157869096417635 1078010566736803644626453)
              ·
                refine ⟨50531745315787670841865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1078010566736803644626453 50531745315787670841865)
                ·
                  rfl

theorem cell21_664269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 6].length) (baseStart_664269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664269 prefixEnd_664269 := by exact prefixLift 664269
  have htrace : WordTrace (prefixWord ++ tailWord_664269) baseStart_664269 baseEnd_664269 := by
    simpa [prefixWord, tailWord_664269, baseEnd_664269] using wordTrace_append hprefix tailTrace_664269
  have hstable : (prefixWord ++ tailWord_664269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664269).length < 2 ^ (prefixWord ++ tailWord_664269).sum := by decide
  have hdescent : baseEnd_664269 < baseStart_664269 := by decide
  rcases family_descends (prefixWord ++ tailWord_664269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664280 : List Nat := [2, 1, 2, 2, 3, 2, 2, 3, 4]
def baseStart_664280 : Nat := 118140960795 + 664280 * 2 ^ 59
def prefixEnd_664280 : Nat := 4983230072969 + 3 ^ 40 * 664280 * 2
def baseEnd_664280 : Nat := 151597746297229437842239

theorem tailTrace_664280 : CollatzResearch.WordTrace tailWord_664280 prefixEnd_664280 151597746297229437842239 := by
  unfold tailWord_664280
  simp only [CollatzResearch.WordTrace]
  refine ⟨12114141016717242418447147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16152188022289656557929529 12114141016717242418447147)
  ·
    refine ⟨18171211525075863627670721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12114141016717242418447147 18171211525075863627670721)
    ·
      refine ⟨13628408643806897720753041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18171211525075863627670721 13628408643806897720753041)
      ·
        refine ⟨10221306482855173290564781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13628408643806897720753041 10221306482855173290564781)
        ·
          refine ⟨3832989931070689983961793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10221306482855173290564781 3832989931070689983961793)
          ·
            refine ⟨2874742448303017487971345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3832989931070689983961793 2874742448303017487971345)
            ·
              refine ⟨2156056836227263115978509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2874742448303017487971345 2156056836227263115978509)
              ·
                refine ⟨808521313585223668491941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2156056836227263115978509 808521313585223668491941)
                ·
                  refine ⟨151597746297229437842239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 808521313585223668491941 151597746297229437842239)
                  ·
                    rfl

theorem cell21_664280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_664280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664280 prefixEnd_664280 := by exact prefixLift 664280
  have htrace : WordTrace (prefixWord ++ tailWord_664280) baseStart_664280 baseEnd_664280 := by
    simpa [prefixWord, tailWord_664280, baseEnd_664280] using wordTrace_append hprefix tailTrace_664280
  have hstable : (prefixWord ++ tailWord_664280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664280).length < 2 ^ (prefixWord ++ tailWord_664280).sum := by decide
  have hdescent : baseEnd_664280 < baseStart_664280 := by decide
  rcases family_descends (prefixWord ++ tailWord_664280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664460 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 7]
def baseStart_664460 : Nat := 118140960795 + 664460 * 2 ^ 59
def prefixEnd_664460 : Nat := 4983230072969 + 3 ^ 40 * 664460 * 2
def baseEnd_664460 : Nat := 151638824749589124841871

theorem tailTrace_664460 : CollatzResearch.WordTrace tailWord_664460 prefixEnd_664460 151638824749589124841871 := by
  unfold tailWord_664460
  simp only [CollatzResearch.WordTrace]
  refine ⟨12117423586391187789223417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16156564781854917052297889 12117423586391187789223417)
  ·
    refine ⟨9088067689793390841917563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12117423586391187789223417 9088067689793390841917563)
    ·
      refine ⟨13632101534690086262876345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9088067689793390841917563 13632101534690086262876345)
      ·
        refine ⟨10224076151017564697157259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13632101534690086262876345 10224076151017564697157259)
        ·
          refine ⟨15336114226526347045735889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10224076151017564697157259 15336114226526347045735889)
          ·
            refine ⟨11502085669894760284301917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15336114226526347045735889 11502085669894760284301917)
            ·
              refine ⟨4313282126210535106613219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11502085669894760284301917 4313282126210535106613219)
              ·
                refine ⟨6469923189315802659919829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4313282126210535106613219 6469923189315802659919829)
                ·
                  refine ⟨151638824749589124841871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6469923189315802659919829 151638824749589124841871)
                  ·
                    rfl

theorem cell21_664460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_664460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664460 prefixEnd_664460 := by exact prefixLift 664460
  have htrace : WordTrace (prefixWord ++ tailWord_664460) baseStart_664460 baseEnd_664460 := by
    simpa [prefixWord, tailWord_664460, baseEnd_664460] using wordTrace_append hprefix tailTrace_664460
  have hstable : (prefixWord ++ tailWord_664460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664460).length < 2 ^ (prefixWord ++ tailWord_664460).sum := by decide
  have hdescent : baseEnd_664460 < baseStart_664460 := by decide
  rcases family_descends (prefixWord ++ tailWord_664460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664581 : List Nat := [1, 3, 1, 1, 2, 3, 1, 9]
def baseStart_664581 : Nat := 118140960795 + 664581 * 2 ^ 59
def prefixEnd_664581 : Nat := 4983230072969 + 3 ^ 40 * 664581 * 2
def baseEnd_664581 : Nat := 50555479532706601108319

theorem tailTrace_664581 : CollatzResearch.WordTrace tailWord_664581 prefixEnd_664581 50555479532706601108319 := by
  unfold tailWord_664581
  simp only [CollatzResearch.WordTrace]
  refine ⟨24239260405344013243601597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16159506936896008829067731 24239260405344013243601597)
  ·
    refine ⟨9089722652004004966350599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24239260405344013243601597 9089722652004004966350599)
    ·
      refine ⟨13634583978006007449525899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9089722652004004966350599 13634583978006007449525899)
      ·
        refine ⟨20451875967009011174288849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13634583978006007449525899 20451875967009011174288849)
        ·
          refine ⟨15338906975256758380716637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20451875967009011174288849 15338906975256758380716637)
          ·
            refine ⟨5752090115721284392768739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15338906975256758380716637 5752090115721284392768739)
            ·
              refine ⟨8628135173581926589153109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5752090115721284392768739 8628135173581926589153109)
              ·
                refine ⟨50555479532706601108319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8628135173581926589153109 50555479532706601108319)
                ·
                  rfl

theorem cell21_664581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 9].length) (baseStart_664581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664581 prefixEnd_664581 := by exact prefixLift 664581
  have htrace : WordTrace (prefixWord ++ tailWord_664581) baseStart_664581 baseEnd_664581 := by
    simpa [prefixWord, tailWord_664581, baseEnd_664581] using wordTrace_append hprefix tailTrace_664581
  have hstable : (prefixWord ++ tailWord_664581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664581).length < 2 ^ (prefixWord ++ tailWord_664581).sum := by decide
  have hdescent : baseEnd_664581 < baseStart_664581 := by decide
  rcases family_descends (prefixWord ++ tailWord_664581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664604 : List Nat := [2, 2, 3, 1, 4, 2, 2, 2, 3]
def baseStart_664604 : Nat := 118140960795 + 664604 * 2 ^ 59
def prefixEnd_664604 : Nat := 4983230072969 + 3 ^ 40 * 664604 * 2
def baseEnd_664604 : Nat := 151671687511476874441577

theorem tailTrace_664604 : CollatzResearch.WordTrace tailWord_664604 prefixEnd_664604 151671687511476874441577 := by
  unfold tailWord_664604
  simp only [CollatzResearch.WordTrace]
  refine ⟨12120049642130344085844433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16160066189507125447792577 12120049642130344085844433)
  ·
    refine ⟨9090037231597758064383325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12120049642130344085844433 9090037231597758064383325)
    ·
      refine ⟨3408763961849159274143747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9090037231597758064383325 3408763961849159274143747)
      ·
        refine ⟨5113145942773738911215621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3408763961849159274143747 5113145942773738911215621)
        ·
          refine ⟨958714864270076045852929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5113145942773738911215621 958714864270076045852929)
          ·
            refine ⟨719036148202557034389697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 958714864270076045852929 719036148202557034389697)
            ·
              refine ⟨539277111151917775792273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719036148202557034389697 539277111151917775792273)
              ·
                refine ⟨404457833363938331844205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539277111151917775792273 404457833363938331844205)
                ·
                  refine ⟨151671687511476874441577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404457833363938331844205 151671687511476874441577)
                  ·
                    rfl

theorem cell21_664604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_664604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664604 prefixEnd_664604 := by exact prefixLift 664604
  have htrace : WordTrace (prefixWord ++ tailWord_664604) baseStart_664604 baseEnd_664604 := by
    simpa [prefixWord, tailWord_664604, baseEnd_664604] using wordTrace_append hprefix tailTrace_664604
  have hstable : (prefixWord ++ tailWord_664604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664604).length < 2 ^ (prefixWord ++ tailWord_664604).sum := by decide
  have hdescent : baseEnd_664604 < baseStart_664604 := by decide
  rcases family_descends (prefixWord ++ tailWord_664604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664615 : List Nat := [1, 1, 7, 1, 1, 1, 3, 6]
def baseStart_664615 : Nat := 118140960795 + 664615 * 2 ^ 59
def prefixEnd_664615 : Nat := 4983230072969 + 3 ^ 40 * 664615 * 2
def baseEnd_664615 : Nat := 50558065953781099919407

theorem tailTrace_664615 : CollatzResearch.WordTrace tailWord_664615 prefixEnd_664615 50558065953781099919407 := by
  unfold tailWord_664615
  simp only [CollatzResearch.WordTrace]
  refine ⟨24240500487220837050339299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16160333658147224700226199 24240500487220837050339299)
  ·
    refine ⟨36360750730831255575508949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24240500487220837050339299 36360750730831255575508949)
    ·
      refine ⟨852205095253857552550991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 36360750730831255575508949 852205095253857552550991)
      ·
        refine ⟨1278307642880786328826487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852205095253857552550991 1278307642880786328826487)
        ·
          refine ⟨1917461464321179493239731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278307642880786328826487 1917461464321179493239731)
          ·
            refine ⟨2876192196481769239859597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917461464321179493239731 2876192196481769239859597)
            ·
              refine ⟨1078572073680663464947349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2876192196481769239859597 1078572073680663464947349)
              ·
                refine ⟨50558065953781099919407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1078572073680663464947349 50558065953781099919407)
                ·
                  rfl

theorem cell21_664615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 6].length) (baseStart_664615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664615 prefixEnd_664615 := by exact prefixLift 664615
  have htrace : WordTrace (prefixWord ++ tailWord_664615) baseStart_664615 baseEnd_664615 := by
    simpa [prefixWord, tailWord_664615, baseEnd_664615] using wordTrace_append hprefix tailTrace_664615
  have hstable : (prefixWord ++ tailWord_664615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664615).length < 2 ^ (prefixWord ++ tailWord_664615).sum := by decide
  have hdescent : baseEnd_664615 < baseStart_664615 := by decide
  rcases family_descends (prefixWord ++ tailWord_664615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664660 : List Nat := [2, 4, 1, 1, 1, 1, 5, 2, 4]
def baseStart_664660 : Nat := 118140960795 + 664660 * 2 ^ 59
def prefixEnd_664660 : Nat := 4983230072969 + 3 ^ 40 * 664660 * 2
def baseEnd_664660 : Nat := 151684467474433221508129

theorem tailTrace_664660 : CollatzResearch.WordTrace tailWord_664660 prefixEnd_664660 151684467474433221508129 := by
  unfold tailWord_664660
  simp only [CollatzResearch.WordTrace]
  refine ⟨12121070886028904867863717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16161427848038539823818289 12121070886028904867863717)
  ·
    refine ⟨2272700791130419662724447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12121070886028904867863717 2272700791130419662724447)
    ·
      refine ⟨3409051186695629494086671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2272700791130419662724447 3409051186695629494086671)
      ·
        refine ⟨5113576780043444241130007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3409051186695629494086671 5113576780043444241130007)
        ·
          refine ⟨7670365170065166361695011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5113576780043444241130007 7670365170065166361695011)
          ·
            refine ⟨11505547755097749542542517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7670365170065166361695011 11505547755097749542542517)
            ·
              refine ⟨1078645102040414019613361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11505547755097749542542517 1078645102040414019613361)
              ·
                refine ⟨808983826530310514710021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078645102040414019613361 808983826530310514710021)
                ·
                  refine ⟨151684467474433221508129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 808983826530310514710021 151684467474433221508129)
                  ·
                    rfl

theorem cell21_664660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_664660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664660 prefixEnd_664660 := by exact prefixLift 664660
  have htrace : WordTrace (prefixWord ++ tailWord_664660) baseStart_664660 baseEnd_664660 := by
    simpa [prefixWord, tailWord_664660, baseEnd_664660] using wordTrace_append hprefix tailTrace_664660
  have hstable : (prefixWord ++ tailWord_664660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664660).length < 2 ^ (prefixWord ++ tailWord_664660).sum := by decide
  have hdescent : baseEnd_664660 < baseStart_664660 := by decide
  rcases family_descends (prefixWord ++ tailWord_664660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664688 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 5]
def baseStart_664688 : Nat := 118140960795 + 664688 * 2 ^ 59
def prefixEnd_664688 : Nat := 4983230072969 + 3 ^ 40 * 664688 * 2
def baseEnd_664688 : Nat := 151690857455911395041405

theorem tailTrace_664688 : CollatzResearch.WordTrace tailWord_664688 prefixEnd_664688 151690857455911395041405 := by
  unfold tailWord_664688
  simp only [CollatzResearch.WordTrace]
  refine ⟨12121581507978185258873359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16162108677304247011831145 12121581507978185258873359)
  ·
    refine ⟨18182372261967277888310039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12121581507978185258873359 18182372261967277888310039)
    ·
      refine ⟨27273558392950916832465059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18182372261967277888310039 27273558392950916832465059)
      ·
        refine ⟨40910337589426375248697589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27273558392950916832465059 40910337589426375248697589)
        ·
          refine ⟨3835344149008722679565399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40910337589426375248697589 3835344149008722679565399)
          ·
            refine ⟨5753016223513084019348099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3835344149008722679565399 5753016223513084019348099)
            ·
              refine ⟨8629524335269626029022149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5753016223513084019348099 8629524335269626029022149)
              ·
                refine ⟨1618035812863054880441653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8629524335269626029022149 1618035812863054880441653)
                ·
                  refine ⟨151690857455911395041405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1618035812863054880441653 151690857455911395041405)
                  ·
                    rfl

theorem cell21_664688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_664688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664688 prefixEnd_664688 := by exact prefixLift 664688
  have htrace : WordTrace (prefixWord ++ tailWord_664688) baseStart_664688 baseEnd_664688 := by
    simpa [prefixWord, tailWord_664688, baseEnd_664688] using wordTrace_append hprefix tailTrace_664688
  have hstable : (prefixWord ++ tailWord_664688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664688).length < 2 ^ (prefixWord ++ tailWord_664688).sum := by decide
  have hdescent : baseEnd_664688 < baseStart_664688 := by decide
  rcases family_descends (prefixWord ++ tailWord_664688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664722 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_664722 : Nat := 118140960795 + 664722 * 2 ^ 59
def prefixEnd_664722 : Nat := 4983230072969 + 3 ^ 40 * 664722 * 2
def baseEnd_664722 : Nat := 151698616719134891474669

theorem tailTrace_664722 : CollatzResearch.WordTrace tailWord_664722 prefixEnd_664722 151698616719134891474669 := by
  unfold tailWord_664722
  simp only [CollatzResearch.WordTrace]
  refine ⟨6061100774458298581121105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16162935398555462882989613 6061100774458298581121105)
  ·
    refine ⟨4545825580843723935840829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6061100774458298581121105 4545825580843723935840829)
    ·
      refine ⟨1704684592816396475940311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4545825580843723935840829 1704684592816396475940311)
      ·
        refine ⟨2557026889224594713910467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1704684592816396475940311 2557026889224594713910467)
        ·
          refine ⟨3835540333836892070865701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2557026889224594713910467 3835540333836892070865701)
          ·
            refine ⟨719163812594417263287319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3835540333836892070865701 719163812594417263287319)
            ·
              refine ⟨1078745718891625894930979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719163812594417263287319 1078745718891625894930979)
              ·
                refine ⟨1618118578337438842396469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078745718891625894930979 1618118578337438842396469)
                ·
                  refine ⟨151698616719134891474669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1618118578337438842396469 151698616719134891474669)
                  ·
                    rfl

theorem cell21_664722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_664722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664722 prefixEnd_664722 := by exact prefixLift 664722
  have htrace : WordTrace (prefixWord ++ tailWord_664722) baseStart_664722 baseEnd_664722 := by
    simpa [prefixWord, tailWord_664722, baseEnd_664722] using wordTrace_append hprefix tailTrace_664722
  have hstable : (prefixWord ++ tailWord_664722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664722).length < 2 ^ (prefixWord ++ tailWord_664722).sum := by decide
  have hdescent : baseEnd_664722 < baseStart_664722 := by decide
  rcases family_descends (prefixWord ++ tailWord_664722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664885 : List Nat := [1, 3, 3, 1, 2, 2, 9]
def baseStart_664885 : Nat := 118140960795 + 664885 * 2 ^ 59
def prefixEnd_664885 : Nat := 4983230072969 + 3 ^ 40 * 664885 * 2
def baseEnd_664885 : Nat := 16859535059986981139741

theorem tailTrace_664885 : CollatzResearch.WordTrace tailWord_664885 prefixEnd_664885 16859535059986981139741 := by
  unfold tailWord_664885
  simp only [CollatzResearch.WordTrace]
  refine ⟨24250348196242673162668109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16166898797495115441778739 24250348196242673162668109)
  ·
    refine ⟨9093880573591002436000541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24250348196242673162668109 9093880573591002436000541)
    ·
      refine ⟨3410205215096625913500203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9093880573591002436000541 3410205215096625913500203)
      ·
        refine ⟨5115307822644938870250305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3410205215096625913500203 5115307822644938870250305)
        ·
          refine ⟨3836480866983704152687729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5115307822644938870250305 3836480866983704152687729)
          ·
            refine ⟨2877360650237778114515797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3836480866983704152687729 2877360650237778114515797)
            ·
              refine ⟨16859535059986981139741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2877360650237778114515797 16859535059986981139741)
              ·
                rfl

theorem cell21_664885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 9].length) (baseStart_664885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664885 prefixEnd_664885 := by exact prefixLift 664885
  have htrace : WordTrace (prefixWord ++ tailWord_664885) baseStart_664885 baseEnd_664885 := by
    simpa [prefixWord, tailWord_664885, baseEnd_664885] using wordTrace_append hprefix tailTrace_664885
  have hstable : (prefixWord ++ tailWord_664885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664885).length < 2 ^ (prefixWord ++ tailWord_664885).sum := by decide
  have hdescent : baseEnd_664885 < baseStart_664885 := by decide
  rcases family_descends (prefixWord ++ tailWord_664885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664916 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 7]
def baseStart_664916 : Nat := 118140960795 + 664916 * 2 ^ 59
def prefixEnd_664916 : Nat := 4983230072969 + 3 ^ 40 * 664916 * 2
def baseEnd_664916 : Nat := 151742890162233665240939

theorem tailTrace_664916 : CollatzResearch.WordTrace tailWord_664916 prefixEnd_664916 151742890162233665240939 := by
  unfold tailWord_664916
  simp only [CollatzResearch.WordTrace]
  refine ⟨12125739429565182728523301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16167652572753576971364401 12125739429565182728523301)
  ·
    refine ⟨2273576143043471761598119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12125739429565182728523301 2273576143043471761598119)
    ·
      refine ⟨3410364214565207642397179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2273576143043471761598119 3410364214565207642397179)
      ·
        refine ⟨5115546321847811463595769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3410364214565207642397179 5115546321847811463595769)
        ·
          refine ⟨3836659741385858597696827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5115546321847811463595769 3836659741385858597696827)
          ·
            refine ⟨5754989612078787896545241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3836659741385858597696827 5754989612078787896545241)
            ·
              refine ⟨4316242209059090922408931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5754989612078787896545241 4316242209059090922408931)
              ·
                refine ⟨6474363313588636383613397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4316242209059090922408931 6474363313588636383613397)
                ·
                  refine ⟨151742890162233665240939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6474363313588636383613397 151742890162233665240939)
                  ·
                    rfl

theorem cell21_664916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_664916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664916 prefixEnd_664916 := by exact prefixLift 664916
  have htrace : WordTrace (prefixWord ++ tailWord_664916) baseStart_664916 baseEnd_664916 := by
    simpa [prefixWord, tailWord_664916, baseEnd_664916] using wordTrace_append hprefix tailTrace_664916
  have hstable : (prefixWord ++ tailWord_664916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664916).length < 2 ^ (prefixWord ++ tailWord_664916).sum := by decide
  have hdescent : baseEnd_664916 < baseStart_664916 := by decide
  rcases family_descends (prefixWord ++ tailWord_664916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664933 : List Nat := [1, 3, 1, 3, 1, 2, 2, 5, 3]
def baseStart_664933 : Nat := 118140960795 + 664933 * 2 ^ 59
def prefixEnd_664933 : Nat := 4983230072969 + 3 ^ 40 * 664933 * 2
def baseEnd_664933 : Nat := 151746769793845413457571

theorem tailTrace_664933 : CollatzResearch.WordTrace tailWord_664933 prefixEnd_664933 151746769793845413457571 := by
  unfold tailWord_664933
  simp only [CollatzResearch.WordTrace]
  refine ⟨24252098900068777360415453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16168065933379184906943635 24252098900068777360415453)
  ·
    refine ⟨9094537087525791510155795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24252098900068777360415453 9094537087525791510155795)
    ·
      refine ⟨13641805631288687265233693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9094537087525791510155795 13641805631288687265233693)
      ·
        refine ⟨5115677111733257724462635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13641805631288687265233693 5115677111733257724462635)
        ·
          refine ⟨7673515667599886586693953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5115677111733257724462635 7673515667599886586693953)
          ·
            refine ⟨5755136750699914940020465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7673515667599886586693953 5755136750699914940020465)
            ·
              refine ⟨4316352563024936205015349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5755136750699914940020465 4316352563024936205015349)
              ·
                refine ⟨404658052783587769220189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4316352563024936205015349 404658052783587769220189)
                ·
                  refine ⟨151746769793845413457571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404658052783587769220189 151746769793845413457571)
                  ·
                    rfl

theorem cell21_664933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_664933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_664933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_664933 prefixEnd_664933 := by exact prefixLift 664933
  have htrace : WordTrace (prefixWord ++ tailWord_664933) baseStart_664933 baseEnd_664933 := by
    simpa [prefixWord, tailWord_664933, baseEnd_664933] using wordTrace_append hprefix tailTrace_664933
  have hstable : (prefixWord ++ tailWord_664933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664933).length < 2 ^ (prefixWord ++ tailWord_664933).sum := by decide
  have hdescent : baseEnd_664933 < baseStart_664933 := by decide
  rcases family_descends (prefixWord ++ tailWord_664933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665009 : List Nat := [1, 2, 2, 4, 1, 1, 1, 6, 3]
def baseStart_665009 : Nat := 118140960795 + 665009 * 2 ^ 59
def prefixEnd_665009 : Nat := 4983230072969 + 3 ^ 40 * 665009 * 2
def baseEnd_665009 : Nat := 151764114029286170190749

theorem tailTrace_665009 : CollatzResearch.WordTrace tailWord_665009 prefixEnd_665009 151764114029286170190749 := by
  unfold tailWord_665009
  simp only [CollatzResearch.WordTrace]
  refine ⟨24254870847793442340182081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16169913898528961560121387 24254870847793442340182081)
  ·
    refine ⟨18191153135845081755136561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24254870847793442340182081 18191153135845081755136561)
    ·
      refine ⟨13643364851883811316352421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18191153135845081755136561 13643364851883811316352421)
      ·
        refine ⟨2558130909728214621816079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13643364851883811316352421 2558130909728214621816079)
        ·
          refine ⟨3837196364592321932724119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558130909728214621816079 3837196364592321932724119)
          ·
            refine ⟨5755794546888482899086179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837196364592321932724119 5755794546888482899086179)
            ·
              refine ⟨8633691820332724348629269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5755794546888482899086179 8633691820332724348629269)
              ·
                refine ⟨404704304078096453841997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8633691820332724348629269 404704304078096453841997)
                ·
                  refine ⟨151764114029286170190749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404704304078096453841997 151764114029286170190749)
                  ·
                    rfl

theorem cell21_665009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 3].length) (baseStart_665009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665009 prefixEnd_665009 := by exact prefixLift 665009
  have htrace : WordTrace (prefixWord ++ tailWord_665009) baseStart_665009 baseEnd_665009 := by
    simpa [prefixWord, tailWord_665009, baseEnd_665009] using wordTrace_append hprefix tailTrace_665009
  have hstable : (prefixWord ++ tailWord_665009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665009).length < 2 ^ (prefixWord ++ tailWord_665009).sum := by decide
  have hdescent : baseEnd_665009 < baseStart_665009 := by decide
  rcases family_descends (prefixWord ++ tailWord_665009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665144 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 5]
def baseStart_665144 : Nat := 118140960795 + 665144 * 2 ^ 59
def prefixEnd_665144 : Nat := 4983230072969 + 3 ^ 40 * 665144 * 2
def baseEnd_665144 : Nat := 151794922868555935440473

theorem tailTrace_665144 : CollatzResearch.WordTrace tailWord_665144 prefixEnd_665144 151794922868555935440473 := by
  unfold tailWord_665144
  simp only [CollatzResearch.WordTrace]
  refine ⟨12129897351152180198173243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16173196468202906930897657 12129897351152180198173243)
  ·
    refine ⟨18194846026728270297259865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12129897351152180198173243 18194846026728270297259865)
    ·
      refine ⟨13646134520046202722944899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18194846026728270297259865 13646134520046202722944899)
      ·
        refine ⟨20469201780069304084417349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13646134520046202722944899 20469201780069304084417349)
        ·
          refine ⟨3837975333762994515828253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20469201780069304084417349 3837975333762994515828253)
          ·
            refine ⟨1439240750161122943435595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3837975333762994515828253 1439240750161122943435595)
            ·
              refine ⟨2158861125241684415153393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439240750161122943435595 2158861125241684415153393)
              ·
                refine ⟨1619145843931263311365045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2158861125241684415153393 1619145843931263311365045)
                ·
                  refine ⟨151794922868555935440473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1619145843931263311365045 151794922868555935440473)
                  ·
                    rfl

theorem cell21_665144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_665144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665144 prefixEnd_665144 := by exact prefixLift 665144
  have htrace : WordTrace (prefixWord ++ tailWord_665144) baseStart_665144 baseEnd_665144 := by
    simpa [prefixWord, tailWord_665144, baseEnd_665144] using wordTrace_append hprefix tailTrace_665144
  have hstable : (prefixWord ++ tailWord_665144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665144).length < 2 ^ (prefixWord ++ tailWord_665144).sum := by decide
  have hdescent : baseEnd_665144 < baseStart_665144 := by decide
  rcases family_descends (prefixWord ++ tailWord_665144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665175 : List Nat := [1, 1, 3, 2, 2, 3, 3, 2, 4]
def baseStart_665175 : Nat := 118140960795 + 665175 * 2 ^ 59
def prefixEnd_665175 : Nat := 4983230072969 + 3 ^ 40 * 665175 * 2
def baseEnd_665175 : Nat := 151801997490906770423743

theorem tailTrace_665175 : CollatzResearch.WordTrace tailWord_665175 prefixEnd_665175 151801997490906770423743 := by
  unfold tailWord_665175
  simp only [CollatzResearch.WordTrace]
  refine ⟨24260925365192052690724979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16173950243461368460483319 24260925365192052690724979)
  ·
    refine ⟨36391388047788079036087469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24260925365192052690724979 36391388047788079036087469)
    ·
      refine ⟨13646770517920529638532801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36391388047788079036087469 13646770517920529638532801)
      ·
        refine ⟨10235077888440397228899601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13646770517920529638532801 10235077888440397228899601)
        ·
          refine ⟨7676308416330297921674701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10235077888440397228899601 7676308416330297921674701)
          ·
            refine ⟨2878615656123861720628013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7676308416330297921674701 2878615656123861720628013)
            ·
              refine ⟨1079480871046448145235505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2878615656123861720628013 1079480871046448145235505)
              ·
                refine ⟨809610653284836108926629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079480871046448145235505 809610653284836108926629)
                ·
                  refine ⟨151801997490906770423743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 809610653284836108926629 151801997490906770423743)
                  ·
                    rfl

theorem cell21_665175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 4].length) (baseStart_665175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665175 prefixEnd_665175 := by exact prefixLift 665175
  have htrace : WordTrace (prefixWord ++ tailWord_665175) baseStart_665175 baseEnd_665175 := by
    simpa [prefixWord, tailWord_665175, baseEnd_665175] using wordTrace_append hprefix tailTrace_665175
  have hstable : (prefixWord ++ tailWord_665175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665175).length < 2 ^ (prefixWord ++ tailWord_665175).sum := by decide
  have hdescent : baseEnd_665175 < baseStart_665175 := by decide
  rcases family_descends (prefixWord ++ tailWord_665175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665206 : List Nat := [5, 1, 1, 2, 2, 2, 1, 7]
def baseStart_665206 : Nat := 118140960795 + 665206 * 2 ^ 59
def prefixEnd_665206 : Nat := 4983230072969 + 3 ^ 40 * 665206 * 2
def baseEnd_665206 : Nat := 50603024037752535135671

theorem tailTrace_665206 : CollatzResearch.WordTrace tailWord_665206 prefixEnd_665206 50603024037752535135671 := by
  unfold tailWord_665206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516378501754984061568967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16174704018719829990068981 1516378501754984061568967)
  ·
    refine ⟨2274567752632476092353451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1516378501754984061568967 2274567752632476092353451)
    ·
      refine ⟨3411851628948714138530177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2274567752632476092353451 3411851628948714138530177)
      ·
        refine ⟨2558888721711535603897633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3411851628948714138530177 2558888721711535603897633)
        ·
          refine ⟨1919166541283651702923225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2558888721711535603897633 1919166541283651702923225)
          ·
            refine ⟨1439374905962738777192419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1919166541283651702923225 1439374905962738777192419)
            ·
              refine ⟨2159062358944108165788629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439374905962738777192419 2159062358944108165788629)
              ·
                refine ⟨50603024037752535135671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2159062358944108165788629 50603024037752535135671)
                ·
                  rfl

theorem cell21_665206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_665206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665206 prefixEnd_665206 := by exact prefixLift 665206
  have htrace : WordTrace (prefixWord ++ tailWord_665206) baseStart_665206 baseEnd_665206 := by
    simpa [prefixWord, tailWord_665206, baseEnd_665206] using wordTrace_append hprefix tailTrace_665206
  have hstable : (prefixWord ++ tailWord_665206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665206).length < 2 ^ (prefixWord ++ tailWord_665206).sum := by decide
  have hdescent : baseEnd_665206 < baseStart_665206 := by decide
  rcases family_descends (prefixWord ++ tailWord_665206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665324 : List Nat := [2, 2, 1, 1, 2, 2, 2, 9]
def baseStart_665324 : Nat := 118140960795 + 665324 * 2 ^ 59
def prefixEnd_665324 : Nat := 4983230072969 + 3 ^ 40 * 665324 * 2
def baseEnd_665324 : Nat := 50612000440305207480035

theorem tailTrace_665324 : CollatzResearch.WordTrace tailWord_665324 prefixEnd_665324 50612000440305207480035 := by
  unfold tailWord_665324
  simp only [CollatzResearch.WordTrace]
  refine ⟨12133179920826125568949513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16177573227768167425266017 12133179920826125568949513)
  ·
    refine ⟨9099884940619594176712135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12133179920826125568949513 9099884940619594176712135)
    ·
      refine ⟨13649827410929391265068203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9099884940619594176712135 13649827410929391265068203)
      ·
        refine ⟨20474741116394086897602305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13649827410929391265068203 20474741116394086897602305)
        ·
          refine ⟨15356055837295565173201729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20474741116394086897602305 15356055837295565173201729)
          ·
            refine ⟨11517041877971673879901297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15356055837295565173201729 11517041877971673879901297)
            ·
              refine ⟨8637781408478755409925973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11517041877971673879901297 8637781408478755409925973)
              ·
                refine ⟨50612000440305207480035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8637781408478755409925973 50612000440305207480035)
                ·
                  rfl

theorem cell21_665324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_665324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665324 prefixEnd_665324 := by exact prefixLift 665324
  have htrace : WordTrace (prefixWord ++ tailWord_665324) baseStart_665324 baseEnd_665324 := by
    simpa [prefixWord, tailWord_665324, baseEnd_665324] using wordTrace_append hprefix tailTrace_665324
  have hstable : (prefixWord ++ tailWord_665324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665324).length < 2 ^ (prefixWord ++ tailWord_665324).sum := by decide
  have hdescent : baseEnd_665324 < baseStart_665324 := by decide
  rcases family_descends (prefixWord ++ tailWord_665324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665355 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 5]
def baseStart_665355 : Nat := 118140960795 + 665355 * 2 ^ 59
def prefixEnd_665355 : Nat := 4983230072969 + 3 ^ 40 * 665355 * 2
def baseEnd_665355 : Nat := 151843075943266457423375

theorem tailTrace_665355 : CollatzResearch.WordTrace tailWord_665355 prefixEnd_665355 151843075943266457423375 := by
  unfold tailWord_665355
  simp only [CollatzResearch.WordTrace]
  refine ⟨24267490504539943432277519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16178327003026628954851679 24267490504539943432277519)
  ·
    refine ⟨36401235756809915148416279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24267490504539943432277519 36401235756809915148416279)
    ·
      refine ⟨54601853635214872722624419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36401235756809915148416279 54601853635214872722624419)
      ·
        refine ⟨81902780452822309083936629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54601853635214872722624419 81902780452822309083936629)
        ·
          refine ⟨7678385667452091476619059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81902780452822309083936629 7678385667452091476619059)
          ·
            refine ⟨11517578501178137214928589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7678385667452091476619059 11517578501178137214928589)
            ·
              refine ⟨4319091937941801455598221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11517578501178137214928589 4319091937941801455598221)
              ·
                refine ⟨1619659476728175545849333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4319091937941801455598221 1619659476728175545849333)
                ·
                  refine ⟨151843075943266457423375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1619659476728175545849333 151843075943266457423375)
                  ·
                    rfl

theorem cell21_665355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 5].length) (baseStart_665355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665355 prefixEnd_665355 := by exact prefixLift 665355
  have htrace : WordTrace (prefixWord ++ tailWord_665355) baseStart_665355 baseEnd_665355 := by
    simpa [prefixWord, tailWord_665355, baseEnd_665355] using wordTrace_append hprefix tailTrace_665355
  have hstable : (prefixWord ++ tailWord_665355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665355).length < 2 ^ (prefixWord ++ tailWord_665355).sum := by decide
  have hdescent : baseEnd_665355 < baseStart_665355 := by decide
  rcases family_descends (prefixWord ++ tailWord_665355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665400 : List Nat := [2, 1, 2, 1, 3, 3, 9]
def baseStart_665400 : Nat := 118140960795 + 665400 * 2 ^ 59
def prefixEnd_665400 : Nat := 4983230072969 + 3 ^ 40 * 665400 * 2
def baseEnd_665400 : Nat := 16872593950706264352587

theorem tailTrace_665400 : CollatzResearch.WordTrace tailWord_665400 prefixEnd_665400 16872593950706264352587 := by
  unfold tailWord_665400
  simp only [CollatzResearch.WordTrace]
  refine ⟨12134565894688458058832827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16179421192917944078443769 12134565894688458058832827)
  ·
    refine ⟨18201848842032687088249241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12134565894688458058832827 18201848842032687088249241)
    ·
      refine ⟨13651386631524515316186931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18201848842032687088249241 13651386631524515316186931)
      ·
        refine ⟨20477079947286772974280397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13651386631524515316186931 20477079947286772974280397)
        ·
          refine ⟨7678904980232539865355149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20477079947286772974280397 7678904980232539865355149)
          ·
            refine ⟨2879589367587202449508181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7678904980232539865355149 2879589367587202449508181)
            ·
              refine ⟨16872593950706264352587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2879589367587202449508181 16872593950706264352587)
              ·
                rfl

theorem cell21_665400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 9].length) (baseStart_665400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665400 prefixEnd_665400 := by exact prefixLift 665400
  have htrace : WordTrace (prefixWord ++ tailWord_665400) baseStart_665400 baseEnd_665400 := by
    simpa [prefixWord, tailWord_665400, baseEnd_665400] using wordTrace_append hprefix tailTrace_665400
  have hstable : (prefixWord ++ tailWord_665400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665400).length < 2 ^ (prefixWord ++ tailWord_665400).sum := by decide
  have hdescent : baseEnd_665400 < baseStart_665400 := by decide
  rcases family_descends (prefixWord ++ tailWord_665400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665493 : List Nat := [1, 3, 2, 1, 1, 3, 5, 5]
def baseStart_665493 : Nat := 118140960795 + 665493 * 2 ^ 59
def prefixEnd_665493 : Nat := 4983230072969 + 3 ^ 40 * 665493 * 2
def baseEnd_665493 : Nat := 50624856474469628041031

theorem tailTrace_665493 : CollatzResearch.WordTrace tailWord_665493 prefixEnd_665493 50624856474469628041031 := by
  unfold tailWord_665493
  simp only [CollatzResearch.WordTrace]
  refine ⟨24272523778039993000801133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16181682518693328667200755 24272523778039993000801133)
  ·
    refine ⟨9102196416764997375300425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24272523778039993000801133 9102196416764997375300425)
    ·
      refine ⟨6826647312573748031475319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9102196416764997375300425 6826647312573748031475319)
      ·
        refine ⟨10239970968860622047212979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6826647312573748031475319 10239970968860622047212979)
        ·
          refine ⟨15359956453290933070819469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10239970968860622047212979 15359956453290933070819469)
          ·
            refine ⟨5759983669984099901557301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15359956453290933070819469 5759983669984099901557301)
            ·
              refine ⟨539998469061009365770997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5759983669984099901557301 539998469061009365770997)
              ·
                refine ⟨50624856474469628041031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 539998469061009365770997 50624856474469628041031)
                ·
                  rfl

theorem cell21_665493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 5].length) (baseStart_665493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665493 prefixEnd_665493 := by exact prefixLift 665493
  have htrace : WordTrace (prefixWord ++ tailWord_665493) baseStart_665493 baseEnd_665493 := by
    simpa [prefixWord, tailWord_665493, baseEnd_665493] using wordTrace_append hprefix tailTrace_665493
  have hstable : (prefixWord ++ tailWord_665493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665493).length < 2 ^ (prefixWord ++ tailWord_665493).sum := by decide
  have hdescent : baseEnd_665493 < baseStart_665493 := by decide
  rcases family_descends (prefixWord ++ tailWord_665493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665628 : List Nat := [2, 2, 3, 1, 3, 10]
def baseStart_665628 : Nat := 118140960795 + 665628 * 2 ^ 59
def prefixEnd_665628 : Nat := 4983230072969 + 3 ^ 40 * 665628 * 2
def baseEnd_665628 : Nat := 5626125120839949976771

theorem tailTrace_665628 : CollatzResearch.WordTrace tailWord_665628 prefixEnd_665628 5626125120839949976771 := by
  unfold tailWord_665628
  simp only [CollatzResearch.WordTrace]
  refine ⟨12138723816275455528482769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16184965088367274037977025 12138723816275455528482769)
  ·
    refine ⟨9104042862206591646362077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12138723816275455528482769 9104042862206591646362077)
    ·
      refine ⟨3414016073327471867385779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9104042862206591646362077 3414016073327471867385779)
      ·
        refine ⟨5121024109991207801078669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3414016073327471867385779 5121024109991207801078669)
        ·
          refine ⟨1920384041246702925404501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5121024109991207801078669 1920384041246702925404501)
          ·
            refine ⟨5626125120839949976771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1920384041246702925404501 5626125120839949976771)
            ·
              rfl

theorem cell21_665628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 10].length) (baseStart_665628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_665628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_665628 prefixEnd_665628 := by exact prefixLift 665628
  have htrace : WordTrace (prefixWord ++ tailWord_665628) baseStart_665628 baseEnd_665628 := by
    simpa [prefixWord, tailWord_665628, baseEnd_665628] using wordTrace_append hprefix tailTrace_665628
  have hstable : (prefixWord ++ tailWord_665628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665628).length < 2 ^ (prefixWord ++ tailWord_665628).sum := by decide
  have hdescent : baseEnd_665628 < baseStart_665628 := by decide
  rcases family_descends (prefixWord ++ tailWord_665628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
