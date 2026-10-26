import V185TrunkScan23Chunk1039

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6156952 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_6156952 : Nat := 118140960795 + 6156952 * 2 ^ 59
def prefixEnd_6156952 : Nat := 4983230072969 + 3 ^ 40 * 6156952 * 2
def baseEnd_6156952 : Nat := 3161475742661100130684699

theorem tailTrace_6156952 : CollatzResearch.WordTrace tailWord_6156952 prefixEnd_6156952 3161475742661100130684699 := by
  unfold tailWord_6156952
  simp only [CollatzResearch.WordTrace]
  refine ⟨112281243995210951265316555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149708325326947935020422073 112281243995210951265316555)
  ·
    refine ⟨168421865992816426897974833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112281243995210951265316555 168421865992816426897974833)
    ·
      refine ⟨126316399494612320173481125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168421865992816426897974833 126316399494612320173481125)
      ·
        refine ⟨23684324905239810032527711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126316399494612320173481125 23684324905239810032527711)
        ·
          refine ⟨35526487357859715048791567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23684324905239810032527711 35526487357859715048791567)
          ·
            refine ⟨53289731036789572573187351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35526487357859715048791567 53289731036789572573187351)
            ·
              refine ⟨79934596555184358859781027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53289731036789572573187351 79934596555184358859781027)
              ·
                refine ⟨119901894832776538289671541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79934596555184358859781027 119901894832776538289671541)
                ·
                  refine ⟨11240802640572800464656707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119901894832776538289671541 11240802640572800464656707)
                  ·
                    refine ⟨16861203960859200696985061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11240802640572800464656707 16861203960859200696985061)
                    ·
                      refine ⟨3161475742661100130684699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16861203960859200696985061 3161475742661100130684699)
                      ·
                        rfl

theorem cell23_6156952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_6156952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156952 prefixEnd_6156952 := by exact prefixLift 6156952
  have htrace : WordTrace (prefixWord ++ tailWord_6156952) baseStart_6156952 baseEnd_6156952 := by
    simpa [prefixWord, tailWord_6156952, baseEnd_6156952] using wordTrace_append hprefix tailTrace_6156952
  have hstable : (prefixWord ++ tailWord_6156952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156952).length < 2 ^ (prefixWord ++ tailWord_6156952).sum := by decide
  have hdescent : baseEnd_6156952 < baseStart_6156952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156955 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 5]
def baseStart_6156955 : Nat := 118140960795 + 6156955 * 2 ^ 59
def prefixEnd_6156955 : Nat := 4983230072969 + 3 ^ 40 * 6156955 * 2
def baseEnd_6156955 : Nat := 3161477283103063618947185

theorem tailTrace_6156955 : CollatzResearch.WordTrace tailWord_6156955 prefixEnd_6156955 3161477283103063618947185 := by
  unfold tailWord_6156955
  simp only [CollatzResearch.WordTrace]
  refine ⟨224562597409411034042992319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149708398272940689361994879 224562597409411034042992319)
  ·
    refine ⟨336843896114116551064488479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224562597409411034042992319 336843896114116551064488479)
    ·
      refine ⟨505265844171174826596732719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336843896114116551064488479 505265844171174826596732719)
      ·
        refine ⟨757898766256762239895099079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505265844171174826596732719 757898766256762239895099079)
        ·
          refine ⟨1136848149385143359842648619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757898766256762239895099079 1136848149385143359842648619)
          ·
            refine ⟨1705272224077715039763972929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136848149385143359842648619 1705272224077715039763972929)
            ·
              refine ⟨1278954168058286279822979697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705272224077715039763972929 1278954168058286279822979697)
              ·
                refine ⟨959215626043714709867234773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278954168058286279822979697 959215626043714709867234773)
                ·
                  refine ⟨22481616235399563512513315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 959215626043714709867234773 22481616235399563512513315)
                  ·
                    refine ⟨33722424353099345268769973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22481616235399563512513315 33722424353099345268769973)
                    ·
                      refine ⟨3161477283103063618947185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33722424353099345268769973 3161477283103063618947185)
                      ·
                        rfl

theorem cell23_6156955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 5].length) (baseStart_6156955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156955 prefixEnd_6156955 := by exact prefixLift 6156955
  have htrace : WordTrace (prefixWord ++ tailWord_6156955) baseStart_6156955 baseEnd_6156955 := by
    simpa [prefixWord, tailWord_6156955, baseEnd_6156955] using wordTrace_append hprefix tailTrace_6156955
  have hstable : (prefixWord ++ tailWord_6156955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156955).length < 2 ^ (prefixWord ++ tailWord_6156955).sum := by decide
  have hdescent : baseEnd_6156955 < baseStart_6156955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156969 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 5, 2, 2]
def baseStart_6156969 : Nat := 118140960795 + 6156969 * 2 ^ 59
def prefixEnd_6156969 : Nat := 4983230072969 + 3 ^ 40 * 6156969 * 2
def baseEnd_6156969 : Nat := 3161484471832226564172121

theorem tailTrace_6156969 : CollatzResearch.WordTrace tailWord_6156969 prefixEnd_6156969 3161484471832226564172121 := by
  unfold tailWord_6156969
  simp only [CollatzResearch.WordTrace]
  refine ⟨224563108031360314434001961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149708738687573542956001307 224563108031360314434001961)
  ·
    refine ⟨168422331023520235825501471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224563108031360314434001961 168422331023520235825501471)
    ·
      refine ⟨252633496535280353738252207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168422331023520235825501471 252633496535280353738252207)
      ·
        refine ⟨378950244802920530607378311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252633496535280353738252207 378950244802920530607378311)
        ·
          refine ⟨568425367204380795911067467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378950244802920530607378311 568425367204380795911067467)
          ·
            refine ⟨852638050806571193866601201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568425367204380795911067467 852638050806571193866601201)
            ·
              refine ⟨639478538104928395399950901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 852638050806571193866601201 639478538104928395399950901)
              ·
                refine ⟨59951112947337037068745397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 639478538104928395399950901 59951112947337037068745397)
                ·
                  refine ⟨5620416838812847225194881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59951112947337037068745397 5620416838812847225194881)
                  ·
                    refine ⟨4215312629109635418896161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5620416838812847225194881 4215312629109635418896161)
                    ·
                      refine ⟨3161484471832226564172121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4215312629109635418896161 3161484471832226564172121)
                      ·
                        rfl

theorem cell23_6156969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 2, 2].length) (baseStart_6156969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156969 prefixEnd_6156969 := by exact prefixLift 6156969
  have htrace : WordTrace (prefixWord ++ tailWord_6156969) baseStart_6156969 baseEnd_6156969 := by
    simpa [prefixWord, tailWord_6156969, baseEnd_6156969] using wordTrace_append hprefix tailTrace_6156969
  have hstable : (prefixWord ++ tailWord_6156969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156969).length < 2 ^ (prefixWord ++ tailWord_6156969).sum := by decide
  have hdescent : baseEnd_6156969 < baseStart_6156969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156973 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_6156973 : Nat := 118140960795 + 6156973 * 2 ^ 59
def prefixEnd_6156973 : Nat := 4983230072969 + 3 ^ 40 * 6156973 * 2
def baseEnd_6156973 : Nat := 3161486525754844548522103

theorem tailTrace_6156973 : CollatzResearch.WordTrace tailWord_6156973 prefixEnd_6156973 3161486525754844548522103 := by
  unfold tailWord_6156973
  simp only [CollatzResearch.WordTrace]
  refine ⟨224563253923345823117147573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149708835948897215411431715 224563253923345823117147573)
  ·
    refine ⟨21052805055313670917232585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224563253923345823117147573 21052805055313670917232585)
    ·
      refine ⟨15789603791485253187924439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21052805055313670917232585 15789603791485253187924439)
      ·
        refine ⟨23684405687227879781886659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15789603791485253187924439 23684405687227879781886659)
        ·
          refine ⟨35526608530841819672829989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23684405687227879781886659 35526608530841819672829989)
          ·
            refine ⟨6661239099532841188655623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35526608530841819672829989 6661239099532841188655623)
            ·
              refine ⟨9991858649299261782983435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6661239099532841188655623 9991858649299261782983435)
              ·
                refine ⟨14987787973948892674475153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9991858649299261782983435 14987787973948892674475153)
                ·
                  refine ⟨11240840980461669505856365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14987787973948892674475153 11240840980461669505856365)
                  ·
                    refine ⟨4215315367673126064696137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11240840980461669505856365 4215315367673126064696137)
                    ·
                      refine ⟨3161486525754844548522103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4215315367673126064696137 3161486525754844548522103)
                      ·
                        rfl

theorem cell23_6156973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_6156973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156973 prefixEnd_6156973 := by exact prefixLift 6156973
  have htrace : WordTrace (prefixWord ++ tailWord_6156973) baseStart_6156973 baseEnd_6156973 := by
    simpa [prefixWord, tailWord_6156973, baseEnd_6156973] using wordTrace_append hprefix tailTrace_6156973
  have hstable : (prefixWord ++ tailWord_6156973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156973).length < 2 ^ (prefixWord ++ tailWord_6156973).sum := by decide
  have hdescent : baseEnd_6156973 < baseStart_6156973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156983 : List Nat := [1, 1, 3, 1, 7, 1, 2, 1, 1, 5]
def baseStart_6156983 : Nat := 118140960795 + 6156983 * 2 ^ 59
def prefixEnd_6156983 : Nat := 4983230072969 + 3 ^ 40 * 6156983 * 2
def baseEnd_6156983 : Nat := 1053830553520463169799019

theorem tailTrace_6156983 : CollatzResearch.WordTrace tailWord_6156983 prefixEnd_6156983 1053830553520463169799019 := by
  unfold tailWord_6156983
  simp only [CollatzResearch.WordTrace]
  refine ⟨224563618653309594825011603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149709079102206396550007735 224563618653309594825011603)
  ·
    refine ⟨336845427979964392237517405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224563618653309594825011603 336845427979964392237517405)
    ·
      refine ⟨126317035492486647089069027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336845427979964392237517405 126317035492486647089069027)
      ·
        refine ⟨189475553238729970633603541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126317035492486647089069027 189475553238729970633603541)
        ·
          refine ⟨4440833279032733686725083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 189475553238729970633603541 4440833279032733686725083)
          ·
            refine ⟨6661249918549100530087625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4440833279032733686725083 6661249918549100530087625)
            ·
              refine ⟨4995937438911825397565719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6661249918549100530087625 4995937438911825397565719)
              ·
                refine ⟨7493906158367738096348579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4995937438911825397565719 7493906158367738096348579)
                ·
                  refine ⟨11240859237551607144522869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7493906158367738096348579 11240859237551607144522869)
                  ·
                    refine ⟨1053830553520463169799019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11240859237551607144522869 1053830553520463169799019)
                    ·
                      rfl

theorem cell23_6156983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_6156983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156983 prefixEnd_6156983 := by exact prefixLift 6156983
  have htrace : WordTrace (prefixWord ++ tailWord_6156983) baseStart_6156983 baseEnd_6156983 := by
    simpa [prefixWord, tailWord_6156983, baseEnd_6156983] using wordTrace_append hprefix tailTrace_6156983
  have hstable : (prefixWord ++ tailWord_6156983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156983).length < 2 ^ (prefixWord ++ tailWord_6156983).sum := by decide
  have hdescent : baseEnd_6156983 < baseStart_6156983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156996 : List Nat := [2, 3, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_6156996 : Nat := 118140960795 + 6156996 * 2 ^ 59
def prefixEnd_6156996 : Nat := 4983230072969 + 3 ^ 40 * 6156996 * 2
def baseEnd_6156996 : Nat := 1053832778603299319511499

theorem tailTrace_6156996 : CollatzResearch.WordTrace tailWord_6156996 prefixEnd_6156996 1053832778603299319511499 := by
  unfold tailWord_6156996
  simp only [CollatzResearch.WordTrace]
  refine ⟨112282046401131249022617421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149709395201508332030156561 112282046401131249022617421)
  ·
    refine ⟨42105767400424218383481533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112282046401131249022617421 42105767400424218383481533)
    ·
      refine ⟨15789662775159081893805575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42105767400424218383481533 15789662775159081893805575)
      ·
        refine ⟨23684494162738622840708363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15789662775159081893805575 23684494162738622840708363)
        ·
          refine ⟨35526741244107934261062545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23684494162738622840708363 35526741244107934261062545)
          ·
            refine ⟨26645055933080950695796909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35526741244107934261062545 26645055933080950695796909)
            ·
              refine ⟨9991895974905356510923841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26645055933080950695796909 9991895974905356510923841)
              ·
                refine ⟨7493921981179017383192881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9991895974905356510923841 7493921981179017383192881)
                ·
                  refine ⟨5620441485884263037394661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7493921981179017383192881 5620441485884263037394661)
                  ·
                    refine ⟨1053832778603299319511499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5620441485884263037394661 1053832778603299319511499)
                    ·
                      rfl

theorem cell23_6156996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_6156996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156996 prefixEnd_6156996 := by exact prefixLift 6156996
  have htrace : WordTrace (prefixWord ++ tailWord_6156996) baseStart_6156996 baseEnd_6156996 := by
    simpa [prefixWord, tailWord_6156996, baseEnd_6156996] using wordTrace_append hprefix tailTrace_6156996
  have hstable : (prefixWord ++ tailWord_6156996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156996).length < 2 ^ (prefixWord ++ tailWord_6156996).sum := by decide
  have hdescent : baseEnd_6156996 < baseStart_6156996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157013 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 1, 6]
def baseStart_6157013 : Nat := 118140960795 + 6157013 * 2 ^ 59
def prefixEnd_6157013 : Nat := 4983230072969 + 3 ^ 40 * 6157013 * 2
def baseEnd_6157013 : Nat := 1053835688327008130673973

theorem tailTrace_6157013 : CollatzResearch.WordTrace tailWord_6157013 prefixEnd_6157013 1053835688327008130673973 := by
  unfold tailWord_6157013
  simp only [CollatzResearch.WordTrace]
  refine ⟨224564712843200909948603693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149709808562133939965735795 224564712843200909948603693)
  ·
    refine ⟨84211767316200341230726385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224564712843200909948603693 84211767316200341230726385)
    ·
      refine ⟨63158825487150255923044789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84211767316200341230726385 63158825487150255923044789)
      ·
        refine ⟨5921139889420336492785449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63158825487150255923044789 5921139889420336492785449)
        ·
          refine ⟨4440854917065252369589087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5921139889420336492785449 4440854917065252369589087)
          ·
            refine ⟨6661282375597878554383631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4440854917065252369589087 6661282375597878554383631)
            ·
              refine ⟨9991923563396817831575447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6661282375597878554383631 9991923563396817831575447)
              ·
                refine ⟨14987885345095226747363171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9991923563396817831575447 14987885345095226747363171)
                ·
                  refine ⟨22481828017642840121044757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14987885345095226747363171 22481828017642840121044757)
                  ·
                    refine ⟨1053835688327008130673973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22481828017642840121044757 1053835688327008130673973)
                    ·
                      rfl

theorem cell23_6157013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_6157013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157013 prefixEnd_6157013 := by exact prefixLift 6157013
  have htrace : WordTrace (prefixWord ++ tailWord_6157013) baseStart_6157013 baseEnd_6157013 := by
    simpa [prefixWord, tailWord_6157013, baseEnd_6157013] using wordTrace_append hprefix tailTrace_6157013
  have hstable : (prefixWord ++ tailWord_6157013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157013).length < 2 ^ (prefixWord ++ tailWord_6157013).sum := by decide
  have hdescent : baseEnd_6157013 < baseStart_6157013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157082 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 9]
def baseStart_6157082 : Nat := 118140960795 + 6157082 * 2 ^ 59
def prefixEnd_6157082 : Nat := 4983230072969 + 3 ^ 40 * 6157082 * 2
def baseEnd_6157082 : Nat := 351282499460687180228789

theorem tailTrace_6157082 : CollatzResearch.WordTrace tailWord_6157082 prefixEnd_6157082 351282499460687180228789 := by
  unfold tailWord_6157082
  simp only [CollatzResearch.WordTrace]
  refine ⟨56141807369987733683216375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149711486319967289821910333 56141807369987733683216375)
  ·
    refine ⟨84212711054981600524824563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56141807369987733683216375 84212711054981600524824563)
    ·
      refine ⟨126319066582472400787236845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84212711054981600524824563 126319066582472400787236845)
      ·
        refine ⟨47369649968427150295213817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126319066582472400787236845 47369649968427150295213817)
        ·
          refine ⟨35527237476320362721410363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47369649968427150295213817 35527237476320362721410363)
          ·
            refine ⟨53290856214480544082115545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35527237476320362721410363 53290856214480544082115545)
            ·
              refine ⟨39968142160860408061586659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53290856214480544082115545 39968142160860408061586659)
              ·
                refine ⟨59952213241290612092379989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39968142160860408061586659 59952213241290612092379989)
                ·
                  refine ⟨351282499460687180228789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59952213241290612092379989 351282499460687180228789)
                  ·
                    rfl

theorem cell23_6157082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_6157082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157082 prefixEnd_6157082 := by exact prefixLift 6157082
  have htrace : WordTrace (prefixWord ++ tailWord_6157082) baseStart_6157082 baseEnd_6157082 := by
    simpa [prefixWord, tailWord_6157082, baseEnd_6157082] using wordTrace_append hprefix tailTrace_6157082
  have hstable : (prefixWord ++ tailWord_6157082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157082).length < 2 ^ (prefixWord ++ tailWord_6157082).sum := by decide
  have hdescent : baseEnd_6157082 < baseStart_6157082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157146 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 2, 5]
def baseStart_6157146 : Nat := 118140960795 + 6157146 * 2 ^ 59
def prefixEnd_6157146 : Nat := 4983230072969 + 3 ^ 40 * 6157146 * 2
def baseEnd_6157146 : Nat := 1053858452636024123886269

theorem tailTrace_6157146 : CollatzResearch.WordTrace tailWord_6157146 prefixEnd_6157146 1053858452636024123886269 := by
  unfold tailWord_6157146
  simp only [CollatzResearch.WordTrace]
  refine ⟨56142390937929768415798823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149713042501146049108796861 56142390937929768415798823)
  ·
    refine ⟨84213586406894652623698235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56142390937929768415798823 84213586406894652623698235)
    ·
      refine ⟨126320379610341978935547353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84213586406894652623698235 126320379610341978935547353)
      ·
        refine ⟨94740284707756484201660515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126320379610341978935547353 94740284707756484201660515)
        ·
          refine ⟨142110427061634726302490773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94740284707756484201660515 142110427061634726302490773)
          ·
            refine ⟨6661426268514127795429255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142110427061634726302490773 6661426268514127795429255)
            ·
              refine ⟨9992139402771191693143883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6661426268514127795429255 9992139402771191693143883)
              ·
                refine ⟨14988209104156787539715825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9992139402771191693143883 14988209104156787539715825)
                ·
                  refine ⟨11241156828117590654786869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14988209104156787539715825 11241156828117590654786869)
                  ·
                    refine ⟨1053858452636024123886269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11241156828117590654786869 1053858452636024123886269)
                    ·
                      rfl

theorem cell23_6157146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_6157146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157146 prefixEnd_6157146 := by exact prefixLift 6157146
  have htrace : WordTrace (prefixWord ++ tailWord_6157146) baseStart_6157146 baseEnd_6157146 := by
    simpa [prefixWord, tailWord_6157146, baseEnd_6157146] using wordTrace_append hprefix tailTrace_6157146
  have hstable : (prefixWord ++ tailWord_6157146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157146).length < 2 ^ (prefixWord ++ tailWord_6157146).sum := by decide
  have hdescent : baseEnd_6157146 < baseStart_6157146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157216 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 5, 1, 3]
def baseStart_6157216 : Nat := 118140960795 + 6157216 * 2 ^ 59
def prefixEnd_6157216 : Nat := 4983230072969 + 3 ^ 40 * 6157216 * 2
def baseEnd_6157216 : Nat := 3161611301553887097783485

theorem tailTrace_6157216 : CollatzResearch.WordTrace tailWord_6157216 prefixEnd_6157216 3161611301553887097783485 := by
  unfold tailWord_6157216
  simp only [CollatzResearch.WordTrace]
  refine ⟨112286058430732737809121751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149714744574310317078829001 112286058430732737809121751)
  ·
    refine ⟨168429087646099106713682627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112286058430732737809121751 168429087646099106713682627)
    ·
      refine ⟨252643631469148660070523941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168429087646099106713682627 252643631469148660070523941)
      ·
        refine ⟨47370680900465373763223239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252643631469148660070523941 47370680900465373763223239)
        ·
          refine ⟨71056021350698060644834859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47370680900465373763223239 71056021350698060644834859)
          ·
            refine ⟨106584032026047090967252289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71056021350698060644834859 106584032026047090967252289)
            ·
              refine ⟨79938024019535318225439217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106584032026047090967252289 79938024019535318225439217)
              ·
                refine ⟨59953518014651488669079413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79938024019535318225439217 59953518014651488669079413)
                ·
                  refine ⟨5620642313873577062726195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59953518014651488669079413 5620642313873577062726195)
                  ·
                    refine ⟨8430963470810365594089293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5620642313873577062726195 8430963470810365594089293)
                    ·
                      refine ⟨3161611301553887097783485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8430963470810365594089293 3161611301553887097783485)
                      ·
                        rfl

theorem cell23_6157216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_6157216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157216 prefixEnd_6157216 := by exact prefixLift 6157216
  have htrace : WordTrace (prefixWord ++ tailWord_6157216) baseStart_6157216 baseEnd_6157216 := by
    simpa [prefixWord, tailWord_6157216, baseEnd_6157216] using wordTrace_append hprefix tailTrace_6157216
  have hstable : (prefixWord ++ tailWord_6157216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157216).length < 2 ^ (prefixWord ++ tailWord_6157216).sum := by decide
  have hdescent : baseEnd_6157216 < baseStart_6157216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157266 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_6157266 : Nat := 118140960795 + 6157266 * 2 ^ 59
def prefixEnd_6157266 : Nat := 4983230072969 + 3 ^ 40 * 6157266 * 2
def baseEnd_6157266 : Nat := 1053878991862203967386085

theorem tailTrace_6157266 : CollatzResearch.WordTrace tailWord_6157266 prefixEnd_6157266 1053878991862203967386085 := by
  unfold tailWord_6157266
  simp only [CollatzResearch.WordTrace]
  refine ⟨56143485127821083539390913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149715960340856222771709101 56143485127821083539390913)
  ·
    refine ⟨42107613845865812654543185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56143485127821083539390913 42107613845865812654543185)
    ·
      refine ⟨31580710384399359490907389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42107613845865812654543185 31580710384399359490907389)
      ·
        refine ⟨11842766394149759809090271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31580710384399359490907389 11842766394149759809090271)
        ·
          refine ⟨17764149591224639713635407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11842766394149759809090271 17764149591224639713635407)
          ·
            refine ⟨26646224386836959570453111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17764149591224639713635407 26646224386836959570453111)
            ·
              refine ⟨39969336580255439355679667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26646224386836959570453111 39969336580255439355679667)
              ·
                refine ⟨59954004870383159033519501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39969336580255439355679667 59954004870383159033519501)
                ·
                  refine ⟨22482751826393684637569813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59954004870383159033519501 22482751826393684637569813)
                  ·
                    refine ⟨1053878991862203967386085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22482751826393684637569813 1053878991862203967386085)
                    ·
                      rfl

theorem cell23_6157266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_6157266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157266 prefixEnd_6157266 := by exact prefixLift 6157266
  have htrace : WordTrace (prefixWord ++ tailWord_6157266) baseStart_6157266 baseEnd_6157266 := by
    simpa [prefixWord, tailWord_6157266, baseEnd_6157266] using wordTrace_append hprefix tailTrace_6157266
  have hstable : (prefixWord ++ tailWord_6157266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157266).length < 2 ^ (prefixWord ++ tailWord_6157266).sum := by decide
  have hdescent : baseEnd_6157266 < baseStart_6157266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157279 : List Nat := [1, 1, 2, 3, 5, 11]
def baseStart_6157279 : Nat := 118140960795 + 6157279 * 2 ^ 59
def prefixEnd_6157279 : Nat := 4983230072969 + 3 ^ 40 * 6157279 * 2
def baseEnd_6157279 : Nat := 13010879221543705149365

theorem tailTrace_6157279 : CollatzResearch.WordTrace tailWord_6157279 prefixEnd_6157279 13010879221543705149365 := by
  unfold tailWord_6157279
  simp only [CollatzResearch.WordTrace]
  refine ⟨224574414660237237377786891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149716276440158158251857927 224574414660237237377786891)
  ·
    refine ⟨336861621990355856066680337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224574414660237237377786891 336861621990355856066680337)
    ·
      refine ⟨252646216492766892050010253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336861621990355856066680337 252646216492766892050010253)
      ·
        refine ⟨94742331184787584518753845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252646216492766892050010253 94742331184787584518753845)
        ·
          refine ⟨8882093548573836048633173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94742331184787584518753845 8882093548573836048633173)
          ·
            refine ⟨13010879221543705149365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8882093548573836048633173 13010879221543705149365)
            ·
              rfl

theorem cell23_6157279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 11].length) (baseStart_6157279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157279 prefixEnd_6157279 := by exact prefixLift 6157279
  have htrace : WordTrace (prefixWord ++ tailWord_6157279) baseStart_6157279 baseEnd_6157279 := by
    simpa [prefixWord, tailWord_6157279, baseEnd_6157279] using wordTrace_append hprefix tailTrace_6157279
  have hstable : (prefixWord ++ tailWord_6157279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157279).length < 2 ^ (prefixWord ++ tailWord_6157279).sum := by decide
  have hdescent : baseEnd_6157279 < baseStart_6157279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157283 : List Nat := [1, 1, 1, 6, 1, 1, 4, 2, 2, 4]
def baseStart_6157283 : Nat := 118140960795 + 6157283 * 2 ^ 59
def prefixEnd_6157283 : Nat := 4983230072969 + 3 ^ 40 * 6157283 * 2
def baseEnd_6157283 : Nat := 1053881901585912778548559

theorem tailTrace_6157283 : CollatzResearch.WordTrace tailWord_6157283 prefixEnd_6157283 1053881901585912778548559 := by
  unfold tailWord_6157283
  simp only [CollatzResearch.WordTrace]
  refine ⟨224574560552222746060932503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149716373701481830707288335 224574560552222746060932503)
  ·
    refine ⟨336861840828334119091398755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224574560552222746060932503 336861840828334119091398755)
    ·
      refine ⟨505292761242501178637098133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336861840828334119091398755 505292761242501178637098133)
      ·
        refine ⟨23685598183242242748613975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 505292761242501178637098133 23685598183242242748613975)
        ·
          refine ⟨35528397274863364122920963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23685598183242242748613975 35528397274863364122920963)
          ·
            refine ⟨53292595912295046184381445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35528397274863364122920963 53292595912295046184381445)
            ·
              refine ⟨9992361733555321159571521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53292595912295046184381445 9992361733555321159571521)
              ·
                refine ⟨7494271300166490869678641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9992361733555321159571521 7494271300166490869678641)
                ·
                  refine ⟨5620703475124868152258981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7494271300166490869678641 5620703475124868152258981)
                  ·
                    refine ⟨1053881901585912778548559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5620703475124868152258981 1053881901585912778548559)
                    ·
                      rfl

theorem cell23_6157283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 4].length) (baseStart_6157283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157283 prefixEnd_6157283 := by exact prefixLift 6157283
  have htrace : WordTrace (prefixWord ++ tailWord_6157283) baseStart_6157283 baseEnd_6157283 := by
    simpa [prefixWord, tailWord_6157283, baseEnd_6157283] using wordTrace_append hprefix tailTrace_6157283
  have hstable : (prefixWord ++ tailWord_6157283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157283).length < 2 ^ (prefixWord ++ tailWord_6157283).sum := by decide
  have hdescent : baseEnd_6157283 < baseStart_6157283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157309 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_6157309 : Nat := 118140960795 + 6157309 * 2 ^ 59
def prefixEnd_6157309 : Nat := 4983230072969 + 3 ^ 40 * 6157309 * 2
def baseEnd_6157309 : Nat := 1053886351751585077973519

theorem tailTrace_6157309 : CollatzResearch.WordTrace tailWord_6157309 prefixEnd_6157309 1053886351751585077973519 := by
  unfold tailWord_6157309
  simp only [CollatzResearch.WordTrace]
  refine ⟨224575508850128552501378981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149717005900085701667585987 224575508850128552501378981)
  ·
    refine ⟨42107907909399103594008559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224575508850128552501378981 42107907909399103594008559)
    ·
      refine ⟨63161861864098655391012839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42107907909399103594008559 63161861864098655391012839)
      ·
        refine ⟨94742792796147983086519259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63161861864098655391012839 94742792796147983086519259)
        ·
          refine ⟨142114189194221974629778889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94742792796147983086519259 142114189194221974629778889)
          ·
            refine ⟨106585641895666480972334167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142114189194221974629778889 106585641895666480972334167)
            ·
              refine ⟨159878462843499721458501251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106585641895666480972334167 159878462843499721458501251)
              ·
                refine ⟨239817694265249582187751877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159878462843499721458501251 239817694265249582187751877)
                ·
                  refine ⟨44965817674734296660203477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 239817694265249582187751877 44965817674734296660203477)
                  ·
                    refine ⟨1053886351751585077973519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44965817674734296660203477 1053886351751585077973519)
                    ·
                      rfl

theorem cell23_6157309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_6157309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157309 prefixEnd_6157309 := by exact prefixLift 6157309
  have htrace : WordTrace (prefixWord ++ tailWord_6157309) baseStart_6157309 baseEnd_6157309 := by
    simpa [prefixWord, tailWord_6157309, baseEnd_6157309] using wordTrace_append hprefix tailTrace_6157309
  have hstable : (prefixWord ++ tailWord_6157309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157309).length < 2 ^ (prefixWord ++ tailWord_6157309).sum := by decide
  have hdescent : baseEnd_6157309 < baseStart_6157309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157330 : List Nat := [3, 2, 5, 1, 1, 1, 10]
def baseStart_6157330 : Nat := 118140960795 + 6157330 * 2 ^ 59
def prefixEnd_6157330 : Nat := 4983230072969 + 3 ^ 40 * 6157330 * 2
def baseEnd_6157330 : Nat := 39032960967265427799481

theorem tailTrace_6157330 : CollatzResearch.WordTrace tailWord_6157330 prefixEnd_6157330 39032960967265427799481 := by
  unfold tailWord_6157330
  simp only [CollatzResearch.WordTrace]
  refine ⟨56144068695763118271973361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149717516522034982058595629 56144068695763118271973361)
  ·
    refine ⟨42108051521822338703980021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56144068695763118271973361 42108051521822338703980021)
    ·
      refine ⟨3947629830170844253498127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42108051521822338703980021 3947629830170844253498127)
      ·
        refine ⟨5921444745256266380247191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3947629830170844253498127 5921444745256266380247191)
        ·
          refine ⟨8882167117884399570370787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5921444745256266380247191 8882167117884399570370787)
          ·
            refine ⟨13323250676826599355556181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8882167117884399570370787 13323250676826599355556181)
            ·
              refine ⟨39032960967265427799481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13323250676826599355556181 39032960967265427799481)
              ·
                rfl

theorem cell23_6157330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 10].length) (baseStart_6157330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157330 prefixEnd_6157330 := by exact prefixLift 6157330
  have htrace : WordTrace (prefixWord ++ tailWord_6157330) baseStart_6157330 baseEnd_6157330 := by
    simpa [prefixWord, tailWord_6157330, baseEnd_6157330] using wordTrace_append hprefix tailTrace_6157330
  have hstable : (prefixWord ++ tailWord_6157330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157330).length < 2 ^ (prefixWord ++ tailWord_6157330).sum := by decide
  have hdescent : baseEnd_6157330 < baseStart_6157330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157340 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_6157340 : Nat := 118140960795 + 6157340 * 2 ^ 59
def prefixEnd_6157340 : Nat := 4983230072969 + 3 ^ 40 * 6157340 * 2
def baseEnd_6157340 : Nat := 3161674973155044612632915

theorem tailTrace_6157340 : CollatzResearch.WordTrace tailWord_6157340 prefixEnd_6157340 3161674973155044612632915 := by
  unfold tailWord_6157340
  simp only [CollatzResearch.WordTrace]
  refine ⟨112288319756508122397878737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149717759675344163197171649 112288319756508122397878737)
  ·
    refine ⟨84216239817381091798409053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112288319756508122397878737 84216239817381091798409053)
    ·
      refine ⟨31581089931517909424403395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84216239817381091798409053 31581089931517909424403395)
      ·
        refine ⟨47371634897276864136605093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31581089931517909424403395 47371634897276864136605093)
        ·
          refine ⟨8882181543239412025613455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47371634897276864136605093 8882181543239412025613455)
          ·
            refine ⟨13323272314859118038420183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8882181543239412025613455 13323272314859118038420183)
            ·
              refine ⟨19984908472288677057630275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13323272314859118038420183 19984908472288677057630275)
              ·
                refine ⟨29977362708433015586445413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19984908472288677057630275 29977362708433015586445413)
                ·
                  refine ⟨5620755507831190422458515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29977362708433015586445413 5620755507831190422458515)
                  ·
                    refine ⟨8431133261746785633687773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5620755507831190422458515 8431133261746785633687773)
                    ·
                      refine ⟨3161674973155044612632915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8431133261746785633687773 3161674973155044612632915)
                      ·
                        rfl

theorem cell23_6157340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_6157340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157340 prefixEnd_6157340 := by exact prefixLift 6157340
  have htrace : WordTrace (prefixWord ++ tailWord_6157340) baseStart_6157340 baseEnd_6157340 := by
    simpa [prefixWord, tailWord_6157340, baseEnd_6157340] using wordTrace_append hprefix tailTrace_6157340
  have hstable : (prefixWord ++ tailWord_6157340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157340).length < 2 ^ (prefixWord ++ tailWord_6157340).sum := by decide
  have hdescent : baseEnd_6157340 < baseStart_6157340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157426 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_6157426 : Nat := 118140960795 + 6157426 * 2 ^ 59
def prefixEnd_6157426 : Nat := 4983230072969 + 3 ^ 40 * 6157426 * 2
def baseEnd_6157426 : Nat := 3161719132491331276157519

theorem tailTrace_6157426 : CollatzResearch.WordTrace tailWord_6157426 prefixEnd_6157426 3161719132491331276157519 := by
  unfold tailWord_6157426
  simp only [CollatzResearch.WordTrace]
  refine ⟨56144944047676170370847033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149719850793803120988925421 56144944047676170370847033)
  ·
    refine ⟨42108708035757127778135275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56144944047676170370847033 42108708035757127778135275)
    ·
      refine ⟨63163062053635691667202913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42108708035757127778135275 63163062053635691667202913)
      ·
        refine ⟨47372296540226768750402185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63163062053635691667202913 47372296540226768750402185)
        ·
          refine ⟨35529222405170076562801639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47372296540226768750402185 35529222405170076562801639)
          ·
            refine ⟨53293833607755114844202459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35529222405170076562801639 53293833607755114844202459)
            ·
              refine ⟨79940750411632672266303689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53293833607755114844202459 79940750411632672266303689)
              ·
                refine ⟨59955562808724504199727767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79940750411632672266303689 59955562808724504199727767)
                ·
                  refine ⟨89933344213086756299591651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59955562808724504199727767 89933344213086756299591651)
                  ·
                    refine ⟨134900016319630134449387477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89933344213086756299591651 134900016319630134449387477)
                    ·
                      refine ⟨3161719132491331276157519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134900016319630134449387477 3161719132491331276157519)
                      ·
                        rfl

theorem cell23_6157426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_6157426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157426 prefixEnd_6157426 := by exact prefixLift 6157426
  have htrace : WordTrace (prefixWord ++ tailWord_6157426) baseStart_6157426 baseEnd_6157426 := by
    simpa [prefixWord, tailWord_6157426, baseEnd_6157426] using wordTrace_append hprefix tailTrace_6157426
  have hstable : (prefixWord ++ tailWord_6157426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157426).length < 2 ^ (prefixWord ++ tailWord_6157426).sum := by decide
  have hdescent : baseEnd_6157426 < baseStart_6157426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157473 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_6157473 : Nat := 118140960795 + 6157473 * 2 ^ 59
def prefixEnd_6157473 : Nat := 4983230072969 + 3 ^ 40 * 6157473 * 2
def baseEnd_6157473 : Nat := 3161743266082092592269803

theorem tailTrace_6157473 : CollatzResearch.WordTrace tailWord_6157473 prefixEnd_6157473 3161743266082092592269803 := by
  unfold tailWord_6157473
  simp only [CollatzResearch.WordTrace]
  refine ⟨224581490421534408510349073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149720993614356272340232715 224581490421534408510349073)
  ·
    refine ⟨168436117816150806382761805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224581490421534408510349073 168436117816150806382761805)
    ·
      refine ⟨63163544181056552393535677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168436117816150806382761805 63163544181056552393535677)
      ·
        refine ⟨23686329067896207147575879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63163544181056552393535677 23686329067896207147575879)
        ·
          refine ⟨35529493601844310721363819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23686329067896207147575879 35529493601844310721363819)
          ·
            refine ⟨53294240402766466082045729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35529493601844310721363819 53294240402766466082045729)
            ·
              refine ⟨39970680302074849561534297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53294240402766466082045729 39970680302074849561534297)
              ·
                refine ⟨29978010226556137171150723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39970680302074849561534297 29978010226556137171150723)
                ·
                  refine ⟨44967015339834205756726085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29978010226556137171150723 44967015339834205756726085)
                  ·
                    refine ⟨8431315376218913579386141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44967015339834205756726085 8431315376218913579386141)
                    ·
                      refine ⟨3161743266082092592269803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8431315376218913579386141 3161743266082092592269803)
                      ·
                        rfl

theorem cell23_6157473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_6157473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157473 prefixEnd_6157473 := by exact prefixLift 6157473
  have htrace : WordTrace (prefixWord ++ tailWord_6157473) baseStart_6157473 baseEnd_6157473 := by
    simpa [prefixWord, tailWord_6157473, baseEnd_6157473] using wordTrace_append hprefix tailTrace_6157473
  have hstable : (prefixWord ++ tailWord_6157473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157473).length < 2 ^ (prefixWord ++ tailWord_6157473).sum := by decide
  have hdescent : baseEnd_6157473 < baseStart_6157473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157490 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_6157490 : Nat := 118140960795 + 6157490 * 2 ^ 59
def prefixEnd_6157490 : Nat := 4983230072969 + 3 ^ 40 * 6157490 * 2
def baseEnd_6157490 : Nat := 3161751995253219025757225

theorem tailTrace_6157490 : CollatzResearch.WordTrace tailWord_6157490 prefixEnd_6157490 3161751995253219025757225 := by
  unfold tailWord_6157490
  simp only [CollatzResearch.WordTrace]
  refine ⟨56145527615618205103429481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149721406974981880275811949 56145527615618205103429481)
  ·
    refine ⟨42109145711713653827572111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56145527615618205103429481 42109145711713653827572111)
    ·
      refine ⟨63163718567570480741358167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42109145711713653827572111 63163718567570480741358167)
      ·
        refine ⟨94745577851355721112037251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63163718567570480741358167 94745577851355721112037251)
        ·
          refine ⟨142118366777033581668055877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94745577851355721112037251 142118366777033581668055877)
          ·
            refine ⟨26647193770693796562760477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142118366777033581668055877 26647193770693796562760477)
            ·
              refine ⟨9992697664010173711035179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26647193770693796562760477 9992697664010173711035179)
              ·
                refine ⟨14989046496015260566552769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9992697664010173711035179 14989046496015260566552769)
                ·
                  refine ⟨11241784872011445424914577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14989046496015260566552769 11241784872011445424914577)
                  ·
                    refine ⟨8431338654008584068685933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11241784872011445424914577 8431338654008584068685933)
                    ·
                      refine ⟨3161751995253219025757225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8431338654008584068685933 3161751995253219025757225)
                      ·
                        rfl

theorem cell23_6157490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_6157490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157490 prefixEnd_6157490 := by exact prefixLift 6157490
  have htrace : WordTrace (prefixWord ++ tailWord_6157490) baseStart_6157490 baseEnd_6157490 := by
    simpa [prefixWord, tailWord_6157490, baseEnd_6157490] using wordTrace_append hprefix tailTrace_6157490
  have hstable : (prefixWord ++ tailWord_6157490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157490).length < 2 ^ (prefixWord ++ tailWord_6157490).sum := by decide
  have hdescent : baseEnd_6157490 < baseStart_6157490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157497 : List Nat := [1, 2, 1, 4, 1, 4, 2, 3, 1, 4]
def baseStart_6157497 : Nat := 118140960795 + 6157497 * 2 ^ 59
def prefixEnd_6157497 : Nat := 4983230072969 + 3 ^ 40 * 6157497 * 2
def baseEnd_6157497 : Nat := 1053918529872600166123231

theorem tailTrace_6157497 : CollatzResearch.WordTrace tailWord_6157497 prefixEnd_6157497 1053918529872600166123231 := by
  unfold tailWord_6157497
  simp only [CollatzResearch.WordTrace]
  refine ⟨224582365773447460609222745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149721577182298307072815163 224582365773447460609222745)
  ·
    refine ⟨168436774330085595456917059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224582365773447460609222745 168436774330085595456917059)
    ·
      refine ⟨252655161495128393185375589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168436774330085595456917059 252655161495128393185375589)
      ·
        refine ⟨47372842780336573722257923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252655161495128393185375589 47372842780336573722257923)
        ·
          refine ⟨71059264170504860583386885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47372842780336573722257923 71059264170504860583386885)
          ·
            refine ⟨13323612031969661359385041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71059264170504860583386885 13323612031969661359385041)
            ·
              refine ⟨9992709023977246019538781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13323612031969661359385041 9992709023977246019538781)
              ·
                refine ⟨3747265883991467257327043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9992709023977246019538781 3747265883991467257327043)
                ·
                  refine ⟨5620898825987200885990565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3747265883991467257327043 5620898825987200885990565)
                  ·
                    refine ⟨1053918529872600166123231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5620898825987200885990565 1053918529872600166123231)
                    ·
                      rfl

theorem cell23_6157497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 1, 4].length) (baseStart_6157497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157497 prefixEnd_6157497 := by exact prefixLift 6157497
  have htrace : WordTrace (prefixWord ++ tailWord_6157497) baseStart_6157497 baseEnd_6157497 := by
    simpa [prefixWord, tailWord_6157497, baseEnd_6157497] using wordTrace_append hprefix tailTrace_6157497
  have hstable : (prefixWord ++ tailWord_6157497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157497).length < 2 ^ (prefixWord ++ tailWord_6157497).sum := by decide
  have hdescent : baseEnd_6157497 < baseStart_6157497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157593 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 7, 3, 3]
def baseStart_6157593 : Nat := 118140960795 + 6157593 * 2 ^ 59
def prefixEnd_6157593 : Nat := 4983230072969 + 3 ^ 40 * 6157593 * 2
def baseEnd_6157593 : Nat := 3161804883760632122769251

theorem tailTrace_6157593 : CollatzResearch.WordTrace tailWord_6157593 prefixEnd_6157593 3161804883760632122769251 := by
  unfold tailWord_6157593
  simp only [CollatzResearch.WordTrace]
  refine ⟨224585867181099669004717433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149723911454066446003144955 224585867181099669004717433)
  ·
    refine ⟨168439400385824751753538075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224585867181099669004717433 168439400385824751753538075)
    ·
      refine ⟨252659100578737127630307113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168439400385824751753538075 252659100578737127630307113)
      ·
        refine ⟨189494325434052845722730335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252659100578737127630307113 189494325434052845722730335)
        ·
          refine ⟨284241488151079268584095503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189494325434052845722730335 284241488151079268584095503)
          ·
            refine ⟨426362232226618902876143255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284241488151079268584095503 426362232226618902876143255)
            ·
              refine ⟨639543348339928354314214883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426362232226618902876143255 639543348339928354314214883)
              ·
                refine ⟨959315022509892531471322325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639543348339928354314214883 959315022509892531471322325)
                ·
                  refine ⟨22483945840075606206359117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 959315022509892531471322325 22483945840075606206359117)
                  ·
                    refine ⟨8431479690028352327384669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22483945840075606206359117 8431479690028352327384669)
                    ·
                      refine ⟨3161804883760632122769251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8431479690028352327384669 3161804883760632122769251)
                      ·
                        rfl

theorem cell23_6157593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_6157593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157593 prefixEnd_6157593 := by exact prefixLift 6157593
  have htrace : WordTrace (prefixWord ++ tailWord_6157593) baseStart_6157593 baseEnd_6157593 := by
    simpa [prefixWord, tailWord_6157593, baseEnd_6157593] using wordTrace_append hprefix tailTrace_6157593
  have hstable : (prefixWord ++ tailWord_6157593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157593).length < 2 ^ (prefixWord ++ tailWord_6157593).sum := by decide
  have hdescent : baseEnd_6157593 < baseStart_6157593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157597 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_6157597 : Nat := 118140960795 + 6157597 * 2 ^ 59
def prefixEnd_6157597 : Nat := 4983230072969 + 3 ^ 40 * 6157597 * 2
def baseEnd_6157597 : Nat := 3161806937683250107119233

theorem tailTrace_6157597 : CollatzResearch.WordTrace tailWord_6157597 prefixEnd_6157597 3161806937683250107119233 := by
  unfold tailWord_6157597
  simp only [CollatzResearch.WordTrace]
  refine ⟨224586013073085177687863045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149724008715390118458575363 224586013073085177687863045)
  ·
    refine ⟨42109877451203470816474321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224586013073085177687863045 42109877451203470816474321)
    ·
      refine ⟨31582408088402603112355741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42109877451203470816474321 31582408088402603112355741)
      ·
        refine ⟨11843403033150976167133403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31582408088402603112355741 11843403033150976167133403)
        ·
          refine ⟨17765104549726464250700105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11843403033150976167133403 17765104549726464250700105)
          ·
            refine ⟨13323828412294848188025079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17765104549726464250700105 13323828412294848188025079)
            ·
              refine ⟨19985742618442272282037619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13323828412294848188025079 19985742618442272282037619)
              ·
                refine ⟨29978613927663408423056429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19985742618442272282037619 29978613927663408423056429)
                ·
                  refine ⟨11241980222873778158646161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29978613927663408423056429 11241980222873778158646161)
                  ·
                    refine ⟨8431485167155333618984621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11241980222873778158646161 8431485167155333618984621)
                    ·
                      refine ⟨3161806937683250107119233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8431485167155333618984621 3161806937683250107119233)
                      ·
                        rfl

theorem cell23_6157597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_6157597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157597 prefixEnd_6157597 := by exact prefixLift 6157597
  have htrace : WordTrace (prefixWord ++ tailWord_6157597) baseStart_6157597 baseEnd_6157597 := by
    simpa [prefixWord, tailWord_6157597, baseEnd_6157597] using wordTrace_append hprefix tailTrace_6157597
  have hstable : (prefixWord ++ tailWord_6157597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157597).length < 2 ^ (prefixWord ++ tailWord_6157597).sum := by decide
  have hdescent : baseEnd_6157597 < baseStart_6157597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157622 : List Nat := [5, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6157622 : Nat := 118140960795 + 6157622 * 2 ^ 59
def prefixEnd_6157622 : Nat := 4983230072969 + 3 ^ 40 * 6157622 * 2
def baseEnd_6157622 : Nat := 3161819774699612509306619

theorem tailTrace_6157622 : CollatzResearch.WordTrace tailWord_6157622 prefixEnd_6157622 3161819774699612509306619 := by
  unfold tailWord_6157622
  simp only [CollatzResearch.WordTrace]
  refine ⟨14036682806124662934845195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149724616598663071305015413 14036682806124662934845195)
  ·
    refine ⟨21055024209186994402267793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14036682806124662934845195 21055024209186994402267793)
    ·
      refine ⟨15791268156890245801700845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21055024209186994402267793 15791268156890245801700845)
      ·
        refine ⟨5921725558833842175637817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15791268156890245801700845 5921725558833842175637817)
        ·
          refine ⟨4441294169125381631728363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5921725558833842175637817 4441294169125381631728363)
          ·
            refine ⟨6661941253688072447592545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4441294169125381631728363 6661941253688072447592545)
            ·
              refine ⟨4996455940266054335694409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6661941253688072447592545 4996455940266054335694409)
              ·
                refine ⟨3747341955199540751770807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4996455940266054335694409 3747341955199540751770807)
                ·
                  refine ⟨5621012932799311127656211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3747341955199540751770807 5621012932799311127656211)
                  ·
                    refine ⟨8431519399198966691484317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5621012932799311127656211 8431519399198966691484317)
                    ·
                      refine ⟨3161819774699612509306619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8431519399198966691484317 3161819774699612509306619)
                      ·
                        rfl

theorem cell23_6157622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6157622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157622 prefixEnd_6157622 := by exact prefixLift 6157622
  have htrace : WordTrace (prefixWord ++ tailWord_6157622) baseStart_6157622 baseEnd_6157622 := by
    simpa [prefixWord, tailWord_6157622, baseEnd_6157622] using wordTrace_append hprefix tailTrace_6157622
  have hstable : (prefixWord ++ tailWord_6157622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157622).length < 2 ^ (prefixWord ++ tailWord_6157622).sum := by decide
  have hdescent : baseEnd_6157622 < baseStart_6157622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157628 : List Nat := [2, 2, 2, 2, 1, 5, 2, 2, 1, 2, 2]
def baseStart_6157628 : Nat := 118140960795 + 6157628 * 2 ^ 59
def prefixEnd_6157628 : Nat := 4983230072969 + 3 ^ 40 * 6157628 * 2
def baseEnd_6157628 : Nat := 3161822855583539485831591

theorem tailTrace_6157628 : CollatzResearch.WordTrace tailWord_6157628 prefixEnd_6157628 3161822855583539485831591 := by
  unfold tailWord_6157628
  simp only [CollatzResearch.WordTrace]
  refine ⟨112293571867986434991120769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149724762490648579988161025 112293571867986434991120769)
  ·
    refine ⟨84220178900989826243340577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112293571867986434991120769 84220178900989826243340577)
    ·
      refine ⟨63165134175742369682505433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84220178900989826243340577 63165134175742369682505433)
      ·
        refine ⟨47373850631806777261879075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63165134175742369682505433 47373850631806777261879075)
        ·
          refine ⟨71060775947710165892818613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47373850631806777261879075 71060775947710165892818613)
          ·
            refine ⟨6661947745097828052451745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71060775947710165892818613 6661947745097828052451745)
            ·
              refine ⟨4996460808823371039338809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6661947745097828052451745 4996460808823371039338809)
              ·
                refine ⟨3747345606617528279504107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4996460808823371039338809 3747345606617528279504107)
                ·
                  refine ⟨5621018409926292419256161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3747345606617528279504107 5621018409926292419256161)
                  ·
                    refine ⟨4215763807444719314442121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5621018409926292419256161 4215763807444719314442121)
                    ·
                      refine ⟨3161822855583539485831591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4215763807444719314442121 3161822855583539485831591)
                      ·
                        rfl

theorem cell23_6157628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_6157628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157628 prefixEnd_6157628 := by exact prefixLift 6157628
  have htrace : WordTrace (prefixWord ++ tailWord_6157628) baseStart_6157628 baseEnd_6157628 := by
    simpa [prefixWord, tailWord_6157628, baseEnd_6157628] using wordTrace_append hprefix tailTrace_6157628
  have hstable : (prefixWord ++ tailWord_6157628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157628).length < 2 ^ (prefixWord ++ tailWord_6157628).sum := by decide
  have hdescent : baseEnd_6157628 < baseStart_6157628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157663 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 4]
def baseStart_6157663 : Nat := 118140960795 + 6157663 * 2 ^ 59
def prefixEnd_6157663 : Nat := 4983230072969 + 3 ^ 40 * 6157663 * 2
def baseEnd_6157663 : Nat := 3161840827406446848893929

theorem tailTrace_6157663 : CollatzResearch.WordTrace tailWord_6157663 prefixEnd_6157663 3161840827406446848893929 := by
  unfold tailWord_6157663
  simp only [CollatzResearch.WordTrace]
  refine ⟨224588420290846070959765643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149725613527230713973177095 224588420290846070959765643)
  ·
    refine ⟨336882630436269106439648465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224588420290846070959765643 336882630436269106439648465)
    ·
      refine ⟨252661972827201829829736349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336882630436269106439648465 252661972827201829829736349)
      ·
        refine ⟨94748239810200686186151131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252661972827201829829736349 94748239810200686186151131)
        ·
          refine ⟨142122359715301029279226697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94748239810200686186151131 142122359715301029279226697)
          ·
            refine ⟨106591769786475771959420023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142122359715301029279226697 106591769786475771959420023)
            ·
              refine ⟨159887654679713657939130035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106591769786475771959420023 159887654679713657939130035)
              ·
                refine ⟨239831482019570486908695053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159887654679713657939130035 239831482019570486908695053)
                ·
                  refine ⟨89936805757338932590760645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239831482019570486908695053 89936805757338932590760645)
                  ·
                    refine ⟨16863151079501049860767621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89936805757338932590760645 16863151079501049860767621)
                    ·
                      refine ⟨3161840827406446848893929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16863151079501049860767621 3161840827406446848893929)
                      ·
                        rfl

theorem cell23_6157663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_6157663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157663 prefixEnd_6157663 := by exact prefixLift 6157663
  have htrace : WordTrace (prefixWord ++ tailWord_6157663) baseStart_6157663 baseEnd_6157663 := by
    simpa [prefixWord, tailWord_6157663, baseEnd_6157663] using wordTrace_append hprefix tailTrace_6157663
  have hstable : (prefixWord ++ tailWord_6157663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157663).length < 2 ^ (prefixWord ++ tailWord_6157663).sum := by decide
  have hdescent : baseEnd_6157663 < baseStart_6157663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157667 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 1, 4, 2]
def baseStart_6157667 : Nat := 118140960795 + 6157667 * 2 ^ 59
def prefixEnd_6157667 : Nat := 4983230072969 + 3 ^ 40 * 6157667 * 2
def baseEnd_6157667 : Nat := 3161842881329064833243911

theorem tailTrace_6157667 : CollatzResearch.WordTrace tailWord_6157667 prefixEnd_6157667 3161842881329064833243911 := by
  unfold tailWord_6157667
  simp only [CollatzResearch.WordTrace]
  refine ⟨224588566182831579642911255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149725710788554386428607503 224588566182831579642911255)
  ·
    refine ⟨336882849274247369464366883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224588566182831579642911255 336882849274247369464366883)
    ·
      refine ⟨505324273911371054196550325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336882849274247369464366883 505324273911371054196550325)
      ·
        refine ⟨47374150679191036330926593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 505324273911371054196550325 47374150679191036330926593)
        ·
          refine ⟨35530613009393277248194945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47374150679191036330926593 35530613009393277248194945)
          ·
            refine ⟨26647959757044957936146209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35530613009393277248194945 26647959757044957936146209)
            ·
              refine ⟨19985969817783718452109657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26647959757044957936146209 19985969817783718452109657)
              ·
                refine ⟨14989477363337788839082243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19985969817783718452109657 14989477363337788839082243)
                ·
                  refine ⟨22484216045006683258623365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14989477363337788839082243 22484216045006683258623365)
                  ·
                    refine ⟨4215790508438753110991881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22484216045006683258623365 4215790508438753110991881)
                    ·
                      refine ⟨3161842881329064833243911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4215790508438753110991881 3161842881329064833243911)
                      ·
                        rfl

theorem cell23_6157667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_6157667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157667 prefixEnd_6157667 := by exact prefixLift 6157667
  have htrace : WordTrace (prefixWord ++ tailWord_6157667) baseStart_6157667 baseEnd_6157667 := by
    simpa [prefixWord, tailWord_6157667, baseEnd_6157667] using wordTrace_append hprefix tailTrace_6157667
  have hstable : (prefixWord ++ tailWord_6157667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157667).length < 2 ^ (prefixWord ++ tailWord_6157667).sum := by decide
  have hdescent : baseEnd_6157667 < baseStart_6157667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157678 : List Nat := [4, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_6157678 : Nat := 118140960795 + 6157678 * 2 ^ 59
def prefixEnd_6157678 : Nat := 4983230072969 + 3 ^ 40 * 6157678 * 2
def baseEnd_6157678 : Nat := 3161848529616264290206361

theorem tailTrace_6157678 : CollatzResearch.WordTrace tailWord_6157678 prefixEnd_6157678 3161848529616264290206361 := by
  unfold tailWord_6157678
  simp only [CollatzResearch.WordTrace]
  refine ⟨28073620923223966065195211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149725978257194485681041125 28073620923223966065195211)
  ·
    refine ⟨42110431384835949097792817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28073620923223966065195211 42110431384835949097792817)
    ·
      refine ⟨31582823538626961823344613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42110431384835949097792817 31582823538626961823344613)
      ·
        refine ⟨5921779413492555341877115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31582823538626961823344613 5921779413492555341877115)
        ·
          refine ⟨8882669120238833012815673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5921779413492555341877115 8882669120238833012815673)
          ·
            refine ⟨6662001840179124759611755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8882669120238833012815673 6662001840179124759611755)
            ·
              refine ⟨9993002760268687139417633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6662001840179124759611755 9993002760268687139417633)
              ·
                refine ⟨7494752070201515354563225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9993002760268687139417633 7494752070201515354563225)
                ·
                  refine ⟨5621064052651136515922419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7494752070201515354563225 5621064052651136515922419)
                  ·
                    refine ⟨8431596078976704773883629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5621064052651136515922419 8431596078976704773883629)
                    ·
                      refine ⟨3161848529616264290206361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8431596078976704773883629 3161848529616264290206361)
                      ·
                        rfl

theorem cell23_6157678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_6157678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157678 prefixEnd_6157678 := by exact prefixLift 6157678
  have htrace : WordTrace (prefixWord ++ tailWord_6157678) baseStart_6157678 baseEnd_6157678 := by
    simpa [prefixWord, tailWord_6157678, baseEnd_6157678] using wordTrace_append hprefix tailTrace_6157678
  have hstable : (prefixWord ++ tailWord_6157678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157678).length < 2 ^ (prefixWord ++ tailWord_6157678).sum := by decide
  have hdescent : baseEnd_6157678 < baseStart_6157678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157713 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_6157713 : Nat := 118140960795 + 6157713 * 2 ^ 59
def prefixEnd_6157713 : Nat := 4983230072969 + 3 ^ 40 * 6157713 * 2
def baseEnd_6157713 : Nat := 3161866501439171653268699

theorem tailTrace_6157713 : CollatzResearch.WordTrace tailWord_6157713 prefixEnd_6157713 3161866501439171653268699 := by
  unfold tailWord_6157713
  simp only [CollatzResearch.WordTrace]
  refine ⟨224590243940664929499085793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149726829293776619666057195 224590243940664929499085793)
  ·
    refine ⟨168442682955498697124314345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224590243940664929499085793 168442682955498697124314345)
    ·
      refine ⟨126332012216624022843235759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168442682955498697124314345 126332012216624022843235759)
      ·
        refine ⟨189498018324936034264853639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126332012216624022843235759 189498018324936034264853639)
        ·
          refine ⟨284247027487404051397280459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189498018324936034264853639 284247027487404051397280459)
          ·
            refine ⟨426370541231106077095920689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284247027487404051397280459 426370541231106077095920689)
            ·
              refine ⟨319777905923329557821940517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426370541231106077095920689 319777905923329557821940517)
              ·
                refine ⟨59958357360624292091613847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319777905923329557821940517 59958357360624292091613847)
                ·
                  refine ⟨89937536040936438137420771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59958357360624292091613847 89937536040936438137420771)
                  ·
                    refine ⟨134906304061404657206131157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89937536040936438137420771 134906304061404657206131157)
                    ·
                      refine ⟨3161866501439171653268699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134906304061404657206131157 3161866501439171653268699)
                      ·
                        rfl

theorem cell23_6157713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_6157713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157713 prefixEnd_6157713 := by exact prefixLift 6157713
  have htrace : WordTrace (prefixWord ++ tailWord_6157713) baseStart_6157713 baseEnd_6157713 := by
    simpa [prefixWord, tailWord_6157713, baseEnd_6157713] using wordTrace_append hprefix tailTrace_6157713
  have hstable : (prefixWord ++ tailWord_6157713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157713).length < 2 ^ (prefixWord ++ tailWord_6157713).sum := by decide
  have hdescent : baseEnd_6157713 < baseStart_6157713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157740 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_6157740 : Nat := 118140960795 + 6157740 * 2 ^ 59
def prefixEnd_6157740 : Nat := 4983230072969 + 3 ^ 40 * 6157740 * 2
def baseEnd_6157740 : Nat := 3161880365416843047631075

theorem tailTrace_6157740 : CollatzResearch.WordTrace tailWord_6157740 prefixEnd_6157740 3161880365416843047631075 := by
  unfold tailWord_6157740
  simp only [CollatzResearch.WordTrace]
  refine ⟨112295614355783556555159337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149727485807711408740212449 112295614355783556555159337)
  ·
    refine ⟨84221710766837667416369503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112295614355783556555159337 84221710766837667416369503)
    ·
      refine ⟨126332566150256501124554255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84221710766837667416369503 126332566150256501124554255)
      ·
        refine ⟨189498849225384751686831383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126332566150256501124554255 189498849225384751686831383)
        ·
          refine ⟨284248273838077127530247075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189498849225384751686831383 284248273838077127530247075)
          ·
            refine ⟨426372410757115691295370613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284248273838077127530247075 426372410757115691295370613)
            ·
              refine ⟨39972413508479596058940995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 426372410757115691295370613 39972413508479596058940995)
              ·
                refine ⟨59958620262719394088411493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39972413508479596058940995 59958620262719394088411493)
                ·
                  refine ⟨11242241299259886391577155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59958620262719394088411493 11242241299259886391577155)
                  ·
                    refine ⟨16863361948889829587365733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11242241299259886391577155 16863361948889829587365733)
                    ·
                      refine ⟨3161880365416843047631075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16863361948889829587365733 3161880365416843047631075)
                      ·
                        rfl

theorem cell23_6157740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_6157740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157740 prefixEnd_6157740 := by exact prefixLift 6157740
  have htrace : WordTrace (prefixWord ++ tailWord_6157740) baseStart_6157740 baseEnd_6157740 := by
    simpa [prefixWord, tailWord_6157740, baseEnd_6157740] using wordTrace_append hprefix tailTrace_6157740
  have hstable : (prefixWord ++ tailWord_6157740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157740).length < 2 ^ (prefixWord ++ tailWord_6157740).sum := by decide
  have hdescent : baseEnd_6157740 < baseStart_6157740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157741 : List Nat := [1, 5, 2, 2, 1, 2, 3, 2, 5]
def baseStart_6157741 : Nat := 118140960795 + 6157741 * 2 ^ 59
def prefixEnd_6157741 : Nat := 4983230072969 + 3 ^ 40 * 6157741 * 2
def baseEnd_6157741 : Nat := 351320097655277504857619

theorem tailTrace_6157741 : CollatzResearch.WordTrace tailWord_6157741 prefixEnd_6157741 351320097655277504857619 := by
  unfold tailWord_6157741
  simp only [CollatzResearch.WordTrace]
  refine ⟨224591265184563490281105077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149727510123042326854070051 224591265184563490281105077)
  ·
    refine ⟨21055431111052827213853601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224591265184563490281105077 21055431111052827213853601)
    ·
      refine ⟨15791573333289620410390201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21055431111052827213853601 15791573333289620410390201)
      ·
        refine ⟨11843679999967215307792651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15791573333289620410390201 11843679999967215307792651)
        ·
          refine ⟨17765519999950822961688977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11843679999967215307792651 17765519999950822961688977)
          ·
            refine ⟨13324139999963117221266733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17765519999950822961688977 13324139999963117221266733)
            ·
              refine ⟨4996552499986168957975025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13324139999963117221266733 4996552499986168957975025)
              ·
                refine ⟨3747414374989626718481269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4996552499986168957975025 3747414374989626718481269)
                ·
                  refine ⟨351320097655277504857619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3747414374989626718481269 351320097655277504857619)
                  ·
                    rfl

theorem cell23_6157741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_6157741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157741 prefixEnd_6157741 := by exact prefixLift 6157741
  have htrace : WordTrace (prefixWord ++ tailWord_6157741) baseStart_6157741 baseEnd_6157741 := by
    simpa [prefixWord, tailWord_6157741, baseEnd_6157741] using wordTrace_append hprefix tailTrace_6157741
  have hstable : (prefixWord ++ tailWord_6157741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157741).length < 2 ^ (prefixWord ++ tailWord_6157741).sum := by decide
  have hdescent : baseEnd_6157741 < baseStart_6157741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157757 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 1, 6, 2]
def baseStart_6157757 : Nat := 118140960795 + 6157757 * 2 ^ 59
def prefixEnd_6157757 : Nat := 4983230072969 + 3 ^ 40 * 6157757 * 2
def baseEnd_6157757 : Nat := 3161889094587969481118497

theorem tailTrace_6157757 : CollatzResearch.WordTrace tailWord_6157757 prefixEnd_6157757 3161889094587969481118497 := by
  unfold tailWord_6157757
  simp only [CollatzResearch.WordTrace]
  refine ⟨224591848752505525013687525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149727899168337016675791683 224591848752505525013687525)
  ·
    refine ⟨42110971641094785940066411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224591848752505525013687525 42110971641094785940066411)
    ·
      refine ⟨63166457461642178910099617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42110971641094785940066411 63166457461642178910099617)
      ·
        refine ⟨47374843096231634182574713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63166457461642178910099617 47374843096231634182574713)
        ·
          refine ⟨35531132322173725636931035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47374843096231634182574713 35531132322173725636931035)
          ·
            refine ⟨53296698483260588455396553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35531132322173725636931035 53296698483260588455396553)
            ·
              refine ⟨39972523862445441341547415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53296698483260588455396553 39972523862445441341547415)
              ·
                refine ⟨59958785793668162012321123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39972523862445441341547415 59958785793668162012321123)
                ·
                  refine ⟨89938178690502243018481685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59958785793668162012321123 89938178690502243018481685)
                  ·
                    refine ⟨4215852126117292641491329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89938178690502243018481685 4215852126117292641491329)
                    ·
                      refine ⟨3161889094587969481118497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4215852126117292641491329 3161889094587969481118497)
                      ·
                        rfl

theorem cell23_6157757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_6157757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157757 prefixEnd_6157757 := by exact prefixLift 6157757
  have htrace : WordTrace (prefixWord ++ tailWord_6157757) baseStart_6157757 baseEnd_6157757 := by
    simpa [prefixWord, tailWord_6157757, baseEnd_6157757] using wordTrace_append hprefix tailTrace_6157757
  have hstable : (prefixWord ++ tailWord_6157757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157757).length < 2 ^ (prefixWord ++ tailWord_6157757).sum := by decide
  have hdescent : baseEnd_6157757 < baseStart_6157757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157760 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 3]
def baseStart_6157760 : Nat := 118140960795 + 6157760 * 2 ^ 59
def prefixEnd_6157760 : Nat := 4983230072969 + 3 ^ 40 * 6157760 * 2
def baseEnd_6157760 : Nat := 3161890635029932969380983

theorem tailTrace_6157760 : CollatzResearch.WordTrace tailWord_6157760 prefixEnd_6157760 3161890635029932969380983 := by
  unfold tailWord_6157760
  simp only [CollatzResearch.WordTrace]
  refine ⟨112295979085747328263023367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149727972114329771017364489 112295979085747328263023367)
  ·
    refine ⟨168443968628620992394535051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112295979085747328263023367 168443968628620992394535051)
    ·
      refine ⟨252665952942931488591802577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168443968628620992394535051 252665952942931488591802577)
      ·
        refine ⟨189499464707198616443851933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252665952942931488591802577 189499464707198616443851933)
        ·
          refine ⟨71062299265199481166444475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189499464707198616443851933 71062299265199481166444475)
          ·
            refine ⟨106593448897799221749666713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71062299265199481166444475 106593448897799221749666713)
            ·
              refine ⟨79945086673349416312250035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106593448897799221749666713 79945086673349416312250035)
              ·
                refine ⟨119917630010024124468375053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79945086673349416312250035 119917630010024124468375053)
                ·
                  refine ⟨44969111253759046675640645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119917630010024124468375053 44969111253759046675640645)
                  ·
                    refine ⟨8431708360079821251682621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44969111253759046675640645 8431708360079821251682621)
                    ·
                      refine ⟨3161890635029932969380983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8431708360079821251682621 3161890635029932969380983)
                      ·
                        rfl

theorem cell23_6157760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_6157760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157760 prefixEnd_6157760 := by exact prefixLift 6157760
  have htrace : WordTrace (prefixWord ++ tailWord_6157760) baseStart_6157760 baseEnd_6157760 := by
    simpa [prefixWord, tailWord_6157760, baseEnd_6157760] using wordTrace_append hprefix tailTrace_6157760
  have hstable : (prefixWord ++ tailWord_6157760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157760).length < 2 ^ (prefixWord ++ tailWord_6157760).sum := by decide
  have hdescent : baseEnd_6157760 < baseStart_6157760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157797 : List Nat := [1, 3, 1, 5, 1, 1, 1, 4, 6]
def baseStart_6157797 : Nat := 118140960795 + 6157797 * 2 ^ 59
def prefixEnd_6157797 : Nat := 4983230072969 + 3 ^ 40 * 6157797 * 2
def baseEnd_6157797 : Nat := 351323292646016591624257

theorem tailTrace_6157797 : CollatzResearch.WordTrace tailWord_6157797 prefixEnd_6157797 351323292646016591624257 := by
  unfold tailWord_6157797
  simp only [CollatzResearch.WordTrace]
  refine ⟨224593307672360611845143645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149728871781573741230095763 224593307672360611845143645)
  ·
    refine ⟨84222490377135229441928867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224593307672360611845143645 84222490377135229441928867)
    ·
      refine ⟨126333735565702844162893301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84222490377135229441928867 126333735565702844162893301)
      ·
        refine ⟨11843787709284641640271247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126333735565702844162893301 11843787709284641640271247)
        ·
          refine ⟨17765681563926962460406871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11843787709284641640271247 17765681563926962460406871)
          ·
            refine ⟨26648522345890443690610307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17765681563926962460406871 26648522345890443690610307)
            ·
              refine ⟨39972783518835665535915461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26648522345890443690610307 39972783518835665535915461)
              ·
                refine ⟨7494896909781687287984149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39972783518835665535915461 7494896909781687287984149)
                ·
                  refine ⟨351323292646016591624257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7494896909781687287984149 351323292646016591624257)
                  ·
                    rfl

theorem cell23_6157797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_6157797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157797 prefixEnd_6157797 := by exact prefixLift 6157797
  have htrace : WordTrace (prefixWord ++ tailWord_6157797) baseStart_6157797 baseEnd_6157797 := by
    simpa [prefixWord, tailWord_6157797, baseEnd_6157797] using wordTrace_append hprefix tailTrace_6157797
  have hstable : (prefixWord ++ tailWord_6157797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157797).length < 2 ^ (prefixWord ++ tailWord_6157797).sum := by decide
  have hdescent : baseEnd_6157797 < baseStart_6157797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157800 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_6157800 : Nat := 118140960795 + 6157800 * 2 ^ 59
def prefixEnd_6157800 : Nat := 4983230072969 + 3 ^ 40 * 6157800 * 2
def baseEnd_6157800 : Nat := 3161911174256112812880799

theorem tailTrace_6157800 : CollatzResearch.WordTrace tailWord_6157800 prefixEnd_6157800 3161911174256112812880799 := by
  unfold tailWord_6157800
  simp only [CollatzResearch.WordTrace]
  refine ⟨112296708545674871678751427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149728944727566495571668569 112296708545674871678751427)
  ·
    refine ⟨168445062818512307518127141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112296708545674871678751427 168445062818512307518127141)
    ·
      refine ⟨31583449278471057659648839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168445062818512307518127141 31583449278471057659648839)
      ·
        refine ⟨47375173917706586489473259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31583449278471057659648839 47375173917706586489473259)
        ·
          refine ⟨71062760876559879734209889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47375173917706586489473259 71062760876559879734209889)
          ·
            refine ⟨53297070657419909800657417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71062760876559879734209889 53297070657419909800657417)
            ·
              refine ⟨39972802993064932350493063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53297070657419909800657417 39972802993064932350493063)
              ·
                refine ⟨59959204489597398525739595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39972802993064932350493063 59959204489597398525739595)
                ·
                  refine ⟨89938806734396097788609393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59959204489597398525739595 89938806734396097788609393)
                  ·
                    refine ⟨67454105050797073341457045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89938806734396097788609393 67454105050797073341457045)
                    ·
                      refine ⟨3161911174256112812880799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67454105050797073341457045 3161911174256112812880799)
                      ·
                        rfl

theorem cell23_6157800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_6157800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157800 prefixEnd_6157800 := by exact prefixLift 6157800
  have htrace : WordTrace (prefixWord ++ tailWord_6157800) baseStart_6157800 baseEnd_6157800 := by
    simpa [prefixWord, tailWord_6157800, baseEnd_6157800] using wordTrace_append hprefix tailTrace_6157800
  have hstable : (prefixWord ++ tailWord_6157800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157800).length < 2 ^ (prefixWord ++ tailWord_6157800).sum := by decide
  have hdescent : baseEnd_6157800 < baseStart_6157800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157817 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 1, 5, 2]
def baseStart_6157817 : Nat := 118140960795 + 6157817 * 2 ^ 59
def prefixEnd_6157817 : Nat := 4983230072969 + 3 ^ 40 * 6157817 * 2
def baseEnd_6157817 : Nat := 3161919903427239246368221

theorem tailTrace_6157817 : CollatzResearch.WordTrace tailWord_6157817 prefixEnd_6157817 3161919903427239246368221 := by
  unfold tailWord_6157817
  simp only [CollatzResearch.WordTrace]
  refine ⟨224594037132288155260871705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149729358088192103507247803 224594037132288155260871705)
  ·
    refine ⟨168445527849216116445653779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224594037132288155260871705 168445527849216116445653779)
    ·
      refine ⟨252668291773824174668480669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168445527849216116445653779 252668291773824174668480669)
      ·
        refine ⟨94750609415184065500680251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252668291773824174668480669 94750609415184065500680251)
        ·
          refine ⟨142125914122776098251020377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94750609415184065500680251 142125914122776098251020377)
          ·
            refine ⟨106594435592082073688265283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142125914122776098251020377 106594435592082073688265283)
            ·
              refine ⟨159891653388123110532397925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106594435592082073688265283 159891653388123110532397925)
              ·
                refine ⟨29979685010273083224824611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159891653388123110532397925 29979685010273083224824611)
                ·
                  refine ⟨44969527515409624837236917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29979685010273083224824611 44969527515409624837236917)
                  ·
                    refine ⟨4215893204569652328490961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44969527515409624837236917 4215893204569652328490961)
                    ·
                      refine ⟨3161919903427239246368221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4215893204569652328490961 3161919903427239246368221)
                      ·
                        rfl

theorem cell23_6157817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_6157817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157817 prefixEnd_6157817 := by exact prefixLift 6157817
  have htrace : WordTrace (prefixWord ++ tailWord_6157817) baseStart_6157817 baseEnd_6157817 := by
    simpa [prefixWord, tailWord_6157817, baseEnd_6157817] using wordTrace_append hprefix tailTrace_6157817
  have hstable : (prefixWord ++ tailWord_6157817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157817).length < 2 ^ (prefixWord ++ tailWord_6157817).sum := by decide
  have hdescent : baseEnd_6157817 < baseStart_6157817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157828 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_6157828 : Nat := 118140960795 + 6157828 * 2 ^ 59
def prefixEnd_6157828 : Nat := 4983230072969 + 3 ^ 40 * 6157828 * 2
def baseEnd_6157828 : Nat := 3161925551714438703330671

theorem tailTrace_6157828 : CollatzResearch.WordTrace tailWord_6157828 prefixEnd_6157828 3161925551714438703330671 := by
  unfold tailWord_6157828
  simp only [CollatzResearch.WordTrace]
  refine ⟨112297219167624152069761069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149729625556832202759681425 112297219167624152069761069)
  ·
    refine ⟨42111457187859057026160401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112297219167624152069761069 42111457187859057026160401)
    ·
      refine ⟨31583592890894292769620301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42111457187859057026160401 31583592890894292769620301)
      ·
        refine ⟨11843847334085359788607613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31583592890894292769620301 11843847334085359788607613)
        ·
          refine ⟨4441442750282009920727855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11843847334085359788607613 4441442750282009920727855)
          ·
            refine ⟨6662164125423014881091783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4441442750282009920727855 6662164125423014881091783)
            ·
              refine ⟨9993246188134522321637675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6662164125423014881091783 9993246188134522321637675)
              ·
                refine ⟨14989869282201783482456513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9993246188134522321637675 14989869282201783482456513)
                ·
                  refine ⟨11242401961651337611842385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14989869282201783482456513 11242401961651337611842385)
                  ·
                    refine ⟨8431801471238503208881789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11242401961651337611842385 8431801471238503208881789)
                    ·
                      refine ⟨3161925551714438703330671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8431801471238503208881789 3161925551714438703330671)
                      ·
                        rfl

theorem cell23_6157828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_6157828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157828 prefixEnd_6157828 := by exact prefixLift 6157828
  have htrace : WordTrace (prefixWord ++ tailWord_6157828) baseStart_6157828 baseEnd_6157828 := by
    simpa [prefixWord, tailWord_6157828, baseEnd_6157828] using wordTrace_append hprefix tailTrace_6157828
  have hstable : (prefixWord ++ tailWord_6157828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157828).length < 2 ^ (prefixWord ++ tailWord_6157828).sum := by decide
  have hdescent : baseEnd_6157828 < baseStart_6157828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157834 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 1, 5, 2]
def baseStart_6157834 : Nat := 118140960795 + 6157834 * 2 ^ 59
def prefixEnd_6157834 : Nat := 4983230072969 + 3 ^ 40 * 6157834 * 2
def baseEnd_6157834 : Nat := 3161928632598365679855643

theorem tailTrace_6157834 : CollatzResearch.WordTrace tailWord_6157834 prefixEnd_6157834 3161928632598365679855643 := by
  unfold tailWord_6157834
  simp only [CollatzResearch.WordTrace]
  refine ⟨56148664293306641791060139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149729771448817711442827037 56148664293306641791060139)
  ·
    refine ⟨84222996439959962686590209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56148664293306641791060139 84222996439959962686590209)
    ·
      refine ⟨63167247329969972014942657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84222996439959962686590209 63167247329969972014942657)
      ·
        refine ⟨47375435497477479011206993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63167247329969972014942657 47375435497477479011206993)
        ·
          refine ⟨35531576623108109258405245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47375435497477479011206993 35531576623108109258405245)
          ·
            refine ⟨13324341233665540971901967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35531576623108109258405245 13324341233665540971901967)
            ·
              refine ⟨19986511850498311457852951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13324341233665540971901967 19986511850498311457852951)
              ·
                refine ⟨29979767775747467186779427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19986511850498311457852951 29979767775747467186779427)
                ·
                  refine ⟨44969651663621200780169141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29979767775747467186779427 44969651663621200780169141)
                  ·
                    refine ⟨4215904843464487573140857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44969651663621200780169141 4215904843464487573140857)
                    ·
                      refine ⟨3161928632598365679855643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4215904843464487573140857 3161928632598365679855643)
                      ·
                        rfl

theorem cell23_6157834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_6157834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157834 prefixEnd_6157834 := by exact prefixLift 6157834
  have htrace : WordTrace (prefixWord ++ tailWord_6157834) baseStart_6157834 baseEnd_6157834 := by
    simpa [prefixWord, tailWord_6157834, baseEnd_6157834] using wordTrace_append hprefix tailTrace_6157834
  have hstable : (prefixWord ++ tailWord_6157834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157834).length < 2 ^ (prefixWord ++ tailWord_6157834).sum := by decide
  have hdescent : baseEnd_6157834 < baseStart_6157834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157841 : List Nat := [1, 2, 2, 1, 1, 2, 6, 3, 1, 1, 3]
def baseStart_6157841 : Nat := 118140960795 + 6157841 * 2 ^ 59
def prefixEnd_6157841 : Nat := 4983230072969 + 3 ^ 40 * 6157841 * 2
def baseEnd_6157841 : Nat := 3161932226962947152468111

theorem tailTrace_6157841 : CollatzResearch.WordTrace tailWord_6157841 prefixEnd_6157841 3161932226962947152468111 := by
  unfold tailWord_6157841
  simp only [CollatzResearch.WordTrace]
  refine ⟨224594912484201207359745377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149729941656134138239830251 224594912484201207359745377)
  ·
    refine ⟨168446184363150905519809033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224594912484201207359745377 168446184363150905519809033)
    ·
      refine ⟨126334638272363179139856775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168446184363150905519809033 126334638272363179139856775)
      ·
        refine ⟨189501957408544768709785163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126334638272363179139856775 189501957408544768709785163)
        ·
          refine ⟨284252936112817153064677745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189501957408544768709785163 284252936112817153064677745)
          ·
            refine ⟨213189702084612864798508309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284252936112817153064677745 213189702084612864798508309)
            ·
              refine ⟨9993267285216228037430077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 213189702084612864798508309 9993267285216228037430077)
              ·
                refine ⟨3747475231956085514036279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9993267285216228037430077 3747475231956085514036279)
                ·
                  refine ⟨5621212847934128271054419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3747475231956085514036279 5621212847934128271054419)
                  ·
                    refine ⟨8431819271901192406581629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5621212847934128271054419 8431819271901192406581629)
                    ·
                      refine ⟨3161932226962947152468111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8431819271901192406581629 3161932226962947152468111)
                      ·
                        rfl

theorem cell23_6157841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 1, 1, 3].length) (baseStart_6157841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157841 prefixEnd_6157841 := by exact prefixLift 6157841
  have htrace : WordTrace (prefixWord ++ tailWord_6157841) baseStart_6157841 baseEnd_6157841 := by
    simpa [prefixWord, tailWord_6157841, baseEnd_6157841] using wordTrace_append hprefix tailTrace_6157841
  have hstable : (prefixWord ++ tailWord_6157841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157841).length < 2 ^ (prefixWord ++ tailWord_6157841).sum := by decide
  have hdescent : baseEnd_6157841 < baseStart_6157841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157877 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_6157877 : Nat := 118140960795 + 6157877 * 2 ^ 59
def prefixEnd_6157877 : Nat := 4983230072969 + 3 ^ 40 * 6157877 * 2
def baseEnd_6157877 : Nat := 3161950712266509011617945

theorem tailTrace_6157877 : CollatzResearch.WordTrace tailWord_6157877 prefixEnd_6157877 3161950712266509011617945 := by
  unfold tailWord_6157877
  simp only [CollatzResearch.WordTrace]
  refine ⟨224596225512070785508055885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149730817008047190338703923 224596225512070785508055885)
  ·
    refine ⟨84223584567026544565520957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224596225512070785508055885 84223584567026544565520957)
    ·
      refine ⟨31583844212634954212070359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84223584567026544565520957 31583844212634954212070359)
      ·
        refine ⟨47375766318952431318105539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31583844212634954212070359 47375766318952431318105539)
        ·
          refine ⟨71063649478428646977158309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47375766318952431318105539 71063649478428646977158309)
          ·
            refine ⟨13324434277205371308217183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71063649478428646977158309 13324434277205371308217183)
            ·
              refine ⟨19986651415808056962325775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13324434277205371308217183 19986651415808056962325775)
              ·
                refine ⟨29979977123712085443488663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19986651415808056962325775 29979977123712085443488663)
                ·
                  refine ⟨44969965685568128165232995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29979977123712085443488663 44969965685568128165232995)
                  ·
                    refine ⟨67454948528352192247849493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44969965685568128165232995 67454948528352192247849493)
                    ·
                      refine ⟨3161950712266509011617945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67454948528352192247849493 3161950712266509011617945)
                      ·
                        rfl

theorem cell23_6157877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_6157877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157877 prefixEnd_6157877 := by exact prefixLift 6157877
  have htrace : WordTrace (prefixWord ++ tailWord_6157877) baseStart_6157877 baseEnd_6157877 := by
    simpa [prefixWord, tailWord_6157877, baseEnd_6157877] using wordTrace_append hprefix tailTrace_6157877
  have hstable : (prefixWord ++ tailWord_6157877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157877).length < 2 ^ (prefixWord ++ tailWord_6157877).sum := by decide
  have hdescent : baseEnd_6157877 < baseStart_6157877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157881 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 3, 2, 2]
def baseStart_6157881 : Nat := 118140960795 + 6157881 * 2 ^ 59
def prefixEnd_6157881 : Nat := 4983230072969 + 3 ^ 40 * 6157881 * 2
def baseEnd_6157881 : Nat := 3161952766189126995967927

theorem tailTrace_6157881 : CollatzResearch.WordTrace tailWord_6157881 prefixEnd_6157881 3161952766189126995967927 := by
  unfold tailWord_6157881
  simp only [CollatzResearch.WordTrace]
  refine ⟨224596371404056294191201497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149730914269370862794134331 224596371404056294191201497)
  ·
    refine ⟨168447278553042220643401123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224596371404056294191201497 168447278553042220643401123)
    ·
      refine ⟨252670917829563330965101685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168447278553042220643401123 252670917829563330965101685)
      ·
        refine ⟨23687898546521562277978283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 252670917829563330965101685 23687898546521562277978283)
        ·
          refine ⟨35531847819782343416967425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23687898546521562277978283 35531847819782343416967425)
          ·
            refine ⟨26648885864836757562725569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35531847819782343416967425 26648885864836757562725569)
            ·
              refine ⟨19986664398627568172044177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26648885864836757562725569 19986664398627568172044177)
              ·
                refine ⟨14989998298970676129033133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19986664398627568172044177 14989998298970676129033133)
                ·
                  refine ⟨5621249362114003548387425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14989998298970676129033133 5621249362114003548387425)
                  ·
                    refine ⟨4215937021585502661290569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5621249362114003548387425 4215937021585502661290569)
                    ·
                      refine ⟨3161952766189126995967927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4215937021585502661290569 3161952766189126995967927)
                      ·
                        rfl

theorem cell23_6157881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_6157881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157881 prefixEnd_6157881 := by exact prefixLift 6157881
  have htrace : WordTrace (prefixWord ++ tailWord_6157881) baseStart_6157881 baseEnd_6157881 := by
    simpa [prefixWord, tailWord_6157881, baseEnd_6157881] using wordTrace_append hprefix tailTrace_6157881
  have hstable : (prefixWord ++ tailWord_6157881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157881).length < 2 ^ (prefixWord ++ tailWord_6157881).sum := by decide
  have hdescent : baseEnd_6157881 < baseStart_6157881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157887 : List Nat := [1, 1, 2, 2, 3, 3, 4, 7]
def baseStart_6157887 : Nat := 118140960795 + 6157887 * 2 ^ 59
def prefixEnd_6157887 : Nat := 4983230072969 + 3 ^ 40 * 6157887 * 2
def baseEnd_6157887 : Nat := 117109475817520517499737

theorem tailTrace_6157887 : CollatzResearch.WordTrace tailWord_6157887 prefixEnd_6157887 117109475817520517499737 := by
  unfold tailWord_6157887
  simp only [CollatzResearch.WordTrace]
  refine ⟨224596590242034557215919915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149731060161356371477279943 224596590242034557215919915)
  ·
    refine ⟨336894885363051835823879873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224596590242034557215919915 336894885363051835823879873)
    ·
      refine ⟨252671164022288876867909905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336894885363051835823879873 252671164022288876867909905)
      ·
        refine ⟨189503373016716657650932429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252671164022288876867909905 189503373016716657650932429)
        ·
          refine ⟨71063764881268746619099661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189503373016716657650932429 71063764881268746619099661)
          ·
            refine ⟨26648911830475779982162373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71063764881268746619099661 26648911830475779982162373)
            ·
              refine ⟨4996670968214208746655445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26648911830475779982162373 4996670968214208746655445)
              ·
                refine ⟨117109475817520517499737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4996670968214208746655445 117109475817520517499737)
                ·
                  rfl

theorem cell23_6157887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 7].length) (baseStart_6157887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157887 prefixEnd_6157887 := by exact prefixLift 6157887
  have htrace : WordTrace (prefixWord ++ tailWord_6157887) baseStart_6157887 baseEnd_6157887 := by
    simpa [prefixWord, tailWord_6157887, baseEnd_6157887] using wordTrace_append hprefix tailTrace_6157887
  have hstable : (prefixWord ++ tailWord_6157887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157887).length < 2 ^ (prefixWord ++ tailWord_6157887).sum := by decide
  have hdescent : baseEnd_6157887 < baseStart_6157887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157897 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 1, 3, 3]
def baseStart_6157897 : Nat := 118140960795 + 6157897 * 2 ^ 59
def prefixEnd_6157897 : Nat := 4983230072969 + 3 ^ 40 * 6157897 * 2
def baseEnd_6157897 : Nat := 3161960981879598933367853

theorem tailTrace_6157897 : CollatzResearch.WordTrace tailWord_6157897 prefixEnd_6157897 3161960981879598933367853 := by
  unfold tailWord_6157897
  simp only [CollatzResearch.WordTrace]
  refine ⟨224596954971998328923783945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149731303314665552615855963 224596954971998328923783945)
  ·
    refine ⟨168447716228998746692837959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224596954971998328923783945 168447716228998746692837959)
    ·
      refine ⟨252671574343498120039256939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168447716228998746692837959 252671574343498120039256939)
      ·
        refine ⟨379007361515247180058885409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252671574343498120039256939 379007361515247180058885409)
        ·
          refine ⟨284255521136435385044164057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379007361515247180058885409 284255521136435385044164057)
          ·
            refine ⟨213191640852326538783123043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284255521136435385044164057 213191640852326538783123043)
            ·
              refine ⟨319787461278489808174684565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213191640852326538783123043 319787461278489808174684565)
              ·
                refine ⟨14990037247429209758188339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 319787461278489808174684565 14990037247429209758188339)
                ·
                  refine ⟨22485055871143814637282509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14990037247429209758188339 22485055871143814637282509)
                  ·
                    refine ⟨8431895951678930488980941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22485055871143814637282509 8431895951678930488980941)
                    ·
                      refine ⟨3161960981879598933367853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8431895951678930488980941 3161960981879598933367853)
                      ·
                        rfl

theorem cell23_6157897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 3, 3].length) (baseStart_6157897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157897 prefixEnd_6157897 := by exact prefixLift 6157897
  have htrace : WordTrace (prefixWord ++ tailWord_6157897) baseStart_6157897 baseEnd_6157897 := by
    simpa [prefixWord, tailWord_6157897, baseEnd_6157897] using wordTrace_append hprefix tailTrace_6157897
  have hstable : (prefixWord ++ tailWord_6157897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157897).length < 2 ^ (prefixWord ++ tailWord_6157897).sum := by decide
  have hdescent : baseEnd_6157897 < baseStart_6157897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157901 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_6157901 : Nat := 118140960795 + 6157901 * 2 ^ 59
def prefixEnd_6157901 : Nat := 4983230072969 + 3 ^ 40 * 6157901 * 2
def baseEnd_6157901 : Nat := 3161963035802216917717835

theorem tailTrace_6157901 : CollatzResearch.WordTrace tailWord_6157901 prefixEnd_6157901 3161963035802216917717835 := by
  unfold tailWord_6157901
  simp only [CollatzResearch.WordTrace]
  refine ⟨224597100863983837606929557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149731400575989225071286371 224597100863983837606929557)
  ·
    refine ⟨10527989102999242387824823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 224597100863983837606929557 10527989102999242387824823)
    ·
      refine ⟨15791983654498863581737235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10527989102999242387824823 15791983654498863581737235)
      ·
        refine ⟨23687975481748295372605853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15791983654498863581737235 23687975481748295372605853)
        ·
          refine ⟨8882990805655610764727195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23687975481748295372605853 8882990805655610764727195)
          ·
            refine ⟨13324486208483416147090793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8882990805655610764727195 13324486208483416147090793)
            ·
              refine ⟨9993364656362562110318095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13324486208483416147090793 9993364656362562110318095)
              ·
                refine ⟨14990046984543843165477143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9993364656362562110318095 14990046984543843165477143)
                ·
                  refine ⟨22485070476815764748215715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14990046984543843165477143 22485070476815764748215715)
                  ·
                    refine ⟨33727605715223647122323573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22485070476815764748215715 33727605715223647122323573)
                    ·
                      refine ⟨3161963035802216917717835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33727605715223647122323573 3161963035802216917717835)
                      ·
                        rfl

theorem cell23_6157901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_6157901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157901 prefixEnd_6157901 := by exact prefixLift 6157901
  have htrace : WordTrace (prefixWord ++ tailWord_6157901) baseStart_6157901 baseEnd_6157901 := by
    simpa [prefixWord, tailWord_6157901, baseEnd_6157901] using wordTrace_append hprefix tailTrace_6157901
  have hstable : (prefixWord ++ tailWord_6157901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157901).length < 2 ^ (prefixWord ++ tailWord_6157901).sum := by decide
  have hdescent : baseEnd_6157901 < baseStart_6157901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157957 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_6157957 : Nat := 118140960795 + 6157957 * 2 ^ 59
def prefixEnd_6157957 : Nat := 4983230072969 + 3 ^ 40 * 6157957 * 2
def baseEnd_6157957 : Nat := 3161991790718868698617577

theorem tailTrace_6157957 : CollatzResearch.WordTrace tailWord_6157957 prefixEnd_6157957 3161991790718868698617577 := by
  unfold tailWord_6157957
  simp only [CollatzResearch.WordTrace]
  refine ⟨224599143351780959170968125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149732762234520639447312083 224599143351780959170968125)
  ·
    refine ⟨84224678756917859689113047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224599143351780959170968125 84224678756917859689113047)
    ·
      refine ⟨126337018135376789533669571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84224678756917859689113047 126337018135376789533669571)
      ·
        refine ⟨189505527203065184300504357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126337018135376789533669571 189505527203065184300504357)
        ·
          refine ⟨35532286350574722056344567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189505527203065184300504357 35532286350574722056344567)
          ·
            refine ⟨53298429525862083084516851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35532286350574722056344567 53298429525862083084516851)
            ·
              refine ⟨79947644288793124626775277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53298429525862083084516851 79947644288793124626775277)
              ·
                refine ⟨29980366608297421735040729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79947644288793124626775277 29980366608297421735040729)
                ·
                  refine ⟨22485274956223066301280547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29980366608297421735040729 22485274956223066301280547)
                  ·
                    refine ⟨33727912434334599451920821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22485274956223066301280547 33727912434334599451920821)
                    ·
                      refine ⟨3161991790718868698617577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33727912434334599451920821 3161991790718868698617577)
                      ·
                        rfl

theorem cell23_6157957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_6157957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157957 prefixEnd_6157957 := by exact prefixLift 6157957
  have htrace : WordTrace (prefixWord ++ tailWord_6157957) baseStart_6157957 baseEnd_6157957 := by
    simpa [prefixWord, tailWord_6157957, baseEnd_6157957] using wordTrace_append hprefix tailTrace_6157957
  have hstable : (prefixWord ++ tailWord_6157957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157957).length < 2 ^ (prefixWord ++ tailWord_6157957).sum := by decide
  have hdescent : baseEnd_6157957 < baseStart_6157957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157984 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 4]
def baseStart_6157984 : Nat := 118140960795 + 6157984 * 2 ^ 59
def prefixEnd_6157984 : Nat := 4983230072969 + 3 ^ 40 * 6157984 * 2
def baseEnd_6157984 : Nat := 3162005654696540092979953

theorem tailTrace_6157984 : CollatzResearch.WordTrace tailWord_6157984 prefixEnd_6157984 3162005654696540092979953 := by
  unfold tailWord_6157984
  simp only [CollatzResearch.WordTrace]
  refine ⟨112300064061341571391100503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149733418748455428521467337 112300064061341571391100503)
  ·
    refine ⟨168450096092012357086650755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112300064061341571391100503 168450096092012357086650755)
    ·
      refine ⟨252675144138018535629976133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168450096092012357086650755 252675144138018535629976133)
      ·
        refine ⟨47376589525878475430620525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252675144138018535629976133 47376589525878475430620525)
        ·
          refine ⟨17766221072204428286482697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47376589525878475430620525 17766221072204428286482697)
          ·
            refine ⟨13324665804153321214862023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17766221072204428286482697 13324665804153321214862023)
            ·
              refine ⟨19986998706229981822293035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13324665804153321214862023 19986998706229981822293035)
              ·
                refine ⟨29980498059344972733439553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19986998706229981822293035 29980498059344972733439553)
                ·
                  refine ⟨22485373544508729550079665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29980498059344972733439553 22485373544508729550079665)
                  ·
                    refine ⟨16864030158381547162559749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22485373544508729550079665 16864030158381547162559749)
                    ·
                      refine ⟨3162005654696540092979953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16864030158381547162559749 3162005654696540092979953)
                      ·
                        rfl

theorem cell23_6157984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_6157984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157984 prefixEnd_6157984 := by exact prefixLift 6157984
  have htrace : WordTrace (prefixWord ++ tailWord_6157984) baseStart_6157984 baseEnd_6157984 := by
    simpa [prefixWord, tailWord_6157984, baseEnd_6157984] using wordTrace_append hprefix tailTrace_6157984
  have hstable : (prefixWord ++ tailWord_6157984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157984).length < 2 ^ (prefixWord ++ tailWord_6157984).sum := by decide
  have hdescent : baseEnd_6157984 < baseStart_6157984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6157988 : List Nat := [2, 3, 1, 2, 2, 2, 2, 3, 2, 2, 2]
def baseStart_6157988 : Nat := 118140960795 + 6157988 * 2 ^ 59
def prefixEnd_6157988 : Nat := 4983230072969 + 3 ^ 40 * 6157988 * 2
def baseEnd_6157988 : Nat := 3162007708619158077329935

theorem tailTrace_6157988 : CollatzResearch.WordTrace tailWord_6157988 prefixEnd_6157988 3162007708619158077329935 := by
  unfold tailWord_6157988
  simp only [CollatzResearch.WordTrace]
  refine ⟨112300137007334325732673309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149733516009779100976897745 112300137007334325732673309)
  ·
    refine ⟨42112551377750372149752491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112300137007334325732673309 42112551377750372149752491)
    ·
      refine ⟨63168827066625558224628737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42112551377750372149752491 63168827066625558224628737)
      ·
        refine ⟨47376620299969168668471553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63168827066625558224628737 47376620299969168668471553)
        ·
          refine ⟨35532465224976876501353665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47376620299969168668471553 35532465224976876501353665)
          ·
            refine ⟨26649348918732657376015249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35532465224976876501353665 26649348918732657376015249)
            ·
              refine ⟨19987011689049493032011437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26649348918732657376015249 19987011689049493032011437)
              ·
                refine ⟨7495129383393559887004289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19987011689049493032011437 7495129383393559887004289)
                ·
                  refine ⟨5621347037545169915253217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7495129383393559887004289 5621347037545169915253217)
                  ·
                    refine ⟨4216010278158877436439913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5621347037545169915253217 4216010278158877436439913)
                    ·
                      refine ⟨3162007708619158077329935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216010278158877436439913 3162007708619158077329935)
                      ·
                        rfl

theorem cell23_6157988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_6157988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6157988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6157988 prefixEnd_6157988 := by exact prefixLift 6157988
  have htrace : WordTrace (prefixWord ++ tailWord_6157988) baseStart_6157988 baseEnd_6157988 := by
    simpa [prefixWord, tailWord_6157988, baseEnd_6157988] using wordTrace_append hprefix tailTrace_6157988
  have hstable : (prefixWord ++ tailWord_6157988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6157988).length < 2 ^ (prefixWord ++ tailWord_6157988).sum := by decide
  have hdescent : baseEnd_6157988 < baseStart_6157988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6157988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158022 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_6158022 : Nat := 118140960795 + 6158022 * 2 ^ 59
def prefixEnd_6158022 : Nat := 4983230072969 + 3 ^ 40 * 6158022 * 2
def baseEnd_6158022 : Nat := 3162025166961410944304779

theorem tailTrace_6158022 : CollatzResearch.WordTrace tailWord_6158022 prefixEnd_6158022 3162025166961410944304779 := by
  unfold tailWord_6158022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018797315517046102252635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149734342731030316848056213 7018797315517046102252635)
  ·
    refine ⟨10528195973275569153378953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7018797315517046102252635 10528195973275569153378953)
    ·
      refine ⟨7896146979956676865034215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10528195973275569153378953 7896146979956676865034215)
      ·
        refine ⟨11844220469935015297551323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7896146979956676865034215 11844220469935015297551323)
        ·
          refine ⟨17766330704902522946326985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11844220469935015297551323 17766330704902522946326985)
          ·
            refine ⟨13324748028676892209745239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17766330704902522946326985 13324748028676892209745239)
            ·
              refine ⟨19987122043015338314617859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13324748028676892209745239 19987122043015338314617859)
              ·
                refine ⟨29980683064523007471926789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19987122043015338314617859 29980683064523007471926789)
                ·
                  refine ⟨5621378074598063900986273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29980683064523007471926789 5621378074598063900986273)
                  ·
                    refine ⟨4216033555948547925739705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5621378074598063900986273 4216033555948547925739705)
                    ·
                      refine ⟨3162025166961410944304779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216033555948547925739705 3162025166961410944304779)
                      ·
                        rfl

theorem cell23_6158022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_6158022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158022 prefixEnd_6158022 := by exact prefixLift 6158022
  have htrace : WordTrace (prefixWord ++ tailWord_6158022) baseStart_6158022 baseEnd_6158022 := by
    simpa [prefixWord, tailWord_6158022, baseEnd_6158022] using wordTrace_append hprefix tailTrace_6158022
  have hstable : (prefixWord ++ tailWord_6158022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158022).length < 2 ^ (prefixWord ++ tailWord_6158022).sum := by decide
  have hdescent : baseEnd_6158022 < baseStart_6158022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158057 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 1, 6, 4]
def baseStart_6158057 : Nat := 118140960795 + 6158057 * 2 ^ 59
def prefixEnd_6158057 : Nat := 4983230072969 + 3 ^ 40 * 6158057 * 2
def baseEnd_6158057 : Nat := 3162043138784318307367117

theorem tailTrace_6158057 : CollatzResearch.WordTrace tailWord_6158057 prefixEnd_6158057 3162043138784318307367117 := by
  unfold tailWord_6158057
  simp only [CollatzResearch.WordTrace]
  refine ⟨224602790651418676249608425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149735193767612450833072283 224602790651418676249608425)
  ·
    refine ⟨168452092988564007187206319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224602790651418676249608425 168452092988564007187206319)
    ·
      refine ⟨252678139482846010780809479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168452092988564007187206319 252678139482846010780809479)
      ·
        refine ⟨379017209224269016171214219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252678139482846010780809479 379017209224269016171214219)
        ·
          refine ⟨568525813836403524256821329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379017209224269016171214219 568525813836403524256821329)
          ·
            refine ⟨426394360377302643192615997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 568525813836403524256821329 426394360377302643192615997)
            ·
              refine ⟨159897885141488491197230999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426394360377302643192615997 159897885141488491197230999)
              ·
                refine ⟨239846827712232736795846499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159897885141488491197230999 239846827712232736795846499)
                ·
                  refine ⟨359770241568349105193769749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239846827712232736795846499 359770241568349105193769749)
                  ·
                    refine ⟨16864230073516364305957957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 359770241568349105193769749 16864230073516364305957957)
                    ·
                      refine ⟨3162043138784318307367117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16864230073516364305957957 3162043138784318307367117)
                      ·
                        rfl

theorem cell23_6158057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_6158057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158057 prefixEnd_6158057 := by exact prefixLift 6158057
  have htrace : WordTrace (prefixWord ++ tailWord_6158057) baseStart_6158057 baseEnd_6158057 := by
    simpa [prefixWord, tailWord_6158057, baseEnd_6158057] using wordTrace_append hprefix tailTrace_6158057
  have hstable : (prefixWord ++ tailWord_6158057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158057).length < 2 ^ (prefixWord ++ tailWord_6158057).sum := by decide
  have hdescent : baseEnd_6158057 < baseStart_6158057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158067 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 8]
def baseStart_6158067 : Nat := 118140960795 + 6158067 * 2 ^ 59
def prefixEnd_6158067 : Nat := 4983230072969 + 3 ^ 40 * 6158067 * 2
def baseEnd_6158067 : Nat := 351338697065651474249119

theorem tailTrace_6158067 : CollatzResearch.WordTrace tailWord_6158067 prefixEnd_6158067 351338697065651474249119 := by
  unfold tailWord_6158067
  simp only [CollatzResearch.WordTrace]
  refine ⟨224603155381382447957472455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149735436920921631971648303 224603155381382447957472455)
  ·
    refine ⟨336904733072073671936208683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224603155381382447957472455 336904733072073671936208683)
    ·
      refine ⟨505357099608110507904313025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336904733072073671936208683 505357099608110507904313025)
      ·
        refine ⟨379017824706082880928234769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505357099608110507904313025 379017824706082880928234769)
        ·
          refine ⟨284263368529562160696176077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379017824706082880928234769 284263368529562160696176077)
          ·
            refine ⟨106598763198585810261066029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284263368529562160696176077 106598763198585810261066029)
            ·
              refine ⟨39974536199469678847899761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106598763198585810261066029 39974536199469678847899761)
              ·
                refine ⟨29980902149602259135924821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39974536199469678847899761 29980902149602259135924821)
                ·
                  refine ⟨351338697065651474249119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29980902149602259135924821 351338697065651474249119)
                  ·
                    rfl

theorem cell23_6158067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 8].length) (baseStart_6158067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158067 prefixEnd_6158067 := by exact prefixLift 6158067
  have htrace : WordTrace (prefixWord ++ tailWord_6158067) baseStart_6158067 baseEnd_6158067 := by
    simpa [prefixWord, tailWord_6158067, baseEnd_6158067] using wordTrace_append hprefix tailTrace_6158067
  have hstable : (prefixWord ++ tailWord_6158067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158067).length < 2 ^ (prefixWord ++ tailWord_6158067).sum := by decide
  have hdescent : baseEnd_6158067 < baseStart_6158067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158078 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_6158078 : Nat := 118140960795 + 6158078 * 2 ^ 59
def prefixEnd_6158078 : Nat := 4983230072969 + 3 ^ 40 * 6158078 * 2
def baseEnd_6158078 : Nat := 3162053921878062725204521

theorem tailTrace_6158078 : CollatzResearch.WordTrace tailWord_6158078 prefixEnd_6158078 3162053921878062725204521 := by
  unfold tailWord_6158078
  simp only [CollatzResearch.WordTrace]
  refine ⟨28075444573042824604515361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149735704389561731224081925 28075444573042824604515361)
  ·
    refine ⟨21056583429782118453386521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28075444573042824604515361 21056583429782118453386521)
    ·
      refine ⟨15792437572336588840039891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21056583429782118453386521 15792437572336588840039891)
      ·
        refine ⟨23688656358504883260059837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15792437572336588840039891 23688656358504883260059837)
        ·
          refine ⟨8883246134439331222522439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23688656358504883260059837 8883246134439331222522439)
          ·
            refine ⟨13324869201658996833783659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8883246134439331222522439 13324869201658996833783659)
            ·
              refine ⟨19987303802488495250675489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13324869201658996833783659 19987303802488495250675489)
              ·
                refine ⟨14990477851866371438006617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19987303802488495250675489 14990477851866371438006617)
                ·
                  refine ⟨11242858388899778578504963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14990477851866371438006617 11242858388899778578504963)
                  ·
                    refine ⟨16864287583349667867757445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11242858388899778578504963 16864287583349667867757445)
                    ·
                      refine ⟨3162053921878062725204521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16864287583349667867757445 3162053921878062725204521)
                      ·
                        rfl

theorem cell23_6158078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_6158078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158078 prefixEnd_6158078 := by exact prefixLift 6158078
  have htrace : WordTrace (prefixWord ++ tailWord_6158078) baseStart_6158078 baseEnd_6158078 := by
    simpa [prefixWord, tailWord_6158078, baseEnd_6158078] using wordTrace_append hprefix tailTrace_6158078
  have hstable : (prefixWord ++ tailWord_6158078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158078).length < 2 ^ (prefixWord ++ tailWord_6158078).sum := by decide
  have hdescent : baseEnd_6158078 < baseStart_6158078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158084 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 8]
def baseStart_6158084 : Nat := 118140960795 + 6158084 * 2 ^ 59
def prefixEnd_6158084 : Nat := 4983230072969 + 3 ^ 40 * 6158084 * 2
def baseEnd_6158084 : Nat := 351339666973554411303277

theorem tailTrace_6158084 : CollatzResearch.WordTrace tailWord_6158084 prefixEnd_6158084 351339666973554411303277 := by
  unfold tailWord_6158084
  simp only [CollatzResearch.WordTrace]
  refine ⟨112301887711160429930420653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149735850281547239907227537 112301887711160429930420653)
  ·
    refine ⟨42113207891685161223907745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112301887711160429930420653 42113207891685161223907745)
    ·
      refine ⟨31584905918763870917930809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42113207891685161223907745 31584905918763870917930809)
      ·
        refine ⟨23688679439072903188448107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31584905918763870917930809 23688679439072903188448107)
        ·
          refine ⟨35533019158609354782672161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23688679439072903188448107 35533019158609354782672161)
          ·
            refine ⟨26649764368957016087004121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35533019158609354782672161 26649764368957016087004121)
            ·
              refine ⟨19987323276717762065253091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26649764368957016087004121 19987323276717762065253091)
              ·
                refine ⟨29980984915076643097879637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19987323276717762065253091 29980984915076643097879637)
                ·
                  refine ⟨351339666973554411303277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29980984915076643097879637 351339666973554411303277)
                  ·
                    rfl

theorem cell23_6158084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_6158084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158084 prefixEnd_6158084 := by exact prefixLift 6158084
  have htrace : WordTrace (prefixWord ++ tailWord_6158084) baseStart_6158084 baseEnd_6158084 := by
    simpa [prefixWord, tailWord_6158084, baseEnd_6158084] using wordTrace_append hprefix tailTrace_6158084
  have hstable : (prefixWord ++ tailWord_6158084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158084).length < 2 ^ (prefixWord ++ tailWord_6158084).sum := by decide
  have hdescent : baseEnd_6158084 < baseStart_6158084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158097 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 2, 9]
def baseStart_6158097 : Nat := 118140960795 + 6158097 * 2 ^ 59
def prefixEnd_6158097 : Nat := 4983230072969 + 3 ^ 40 * 6158097 * 2
def baseEnd_6158097 : Nat := 1054021226003499383622311

theorem tailTrace_6158097 : CollatzResearch.WordTrace tailWord_6158097 prefixEnd_6158097 1054021226003499383622311 := by
  unfold tailWord_6158097
  simp only [CollatzResearch.WordTrace]
  refine ⟨224604249571273763081064545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149736166380849175387376363 224604249571273763081064545)
  ·
    refine ⟨168453187178455322310798409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224604249571273763081064545 168453187178455322310798409)
    ·
      refine ⟨126339890383841491733098807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168453187178455322310798409 126339890383841491733098807)
      ·
        refine ⟨189509835575762237599648211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126339890383841491733098807 189509835575762237599648211)
        ·
          refine ⟨284264753363643356399472317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189509835575762237599648211 284264753363643356399472317)
          ·
            refine ⟨106599282511366258649802119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284264753363643356399472317 106599282511366258649802119)
            ·
              refine ⟨159898923767049387974703179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106599282511366258649802119 159898923767049387974703179)
              ·
                refine ⟨239848385650574081962054769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159898923767049387974703179 239848385650574081962054769)
                ·
                  refine ⟨179886289237930561471541077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239848385650574081962054769 179886289237930561471541077)
                  ·
                    refine ⟨1054021226003499383622311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 179886289237930561471541077 1054021226003499383622311)
                    ·
                      rfl

theorem cell23_6158097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_6158097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158097 prefixEnd_6158097 := by exact prefixLift 6158097
  have htrace : WordTrace (prefixWord ++ tailWord_6158097) baseStart_6158097 baseEnd_6158097 := by
    simpa [prefixWord, tailWord_6158097, baseEnd_6158097] using wordTrace_append hprefix tailTrace_6158097
  have hstable : (prefixWord ++ tailWord_6158097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158097).length < 2 ^ (prefixWord ++ tailWord_6158097).sum := by decide
  have hdescent : baseEnd_6158097 < baseStart_6158097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158101 : List Nat := [1, 3, 2, 1, 2, 3, 4, 1, 6]
def baseStart_6158101 : Nat := 118140960795 + 6158101 * 2 ^ 59
def prefixEnd_6158101 : Nat := 4983230072969 + 3 ^ 40 * 6158101 * 2
def baseEnd_6158101 : Nat := 351340636881457348357435

theorem tailTrace_6158101 : CollatzResearch.WordTrace tailWord_6158101 prefixEnd_6158101 351340636881457348357435 := by
  unfold tailWord_6158101
  simp only [CollatzResearch.WordTrace]
  refine ⟨224604395463259271764210157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149736263642172847842806771 224604395463259271764210157)
  ·
    refine ⟨84226648298722226911578809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224604395463259271764210157 84226648298722226911578809)
    ·
      refine ⟨63169986224041670183684107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84226648298722226911578809 63169986224041670183684107)
      ·
        refine ⟨94754979336062505275526161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63169986224041670183684107 94754979336062505275526161)
        ·
          refine ⟨71066234502046878956644621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94754979336062505275526161 71066234502046878956644621)
          ·
            refine ⟨26649837938267579608741733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71066234502046878956644621 26649837938267579608741733)
            ·
              refine ⟨4996844613425171176639075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26649837938267579608741733 4996844613425171176639075)
              ·
                refine ⟨7495266920137756764958613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4996844613425171176639075 7495266920137756764958613)
                ·
                  refine ⟨351340636881457348357435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7495266920137756764958613 351340636881457348357435)
                  ·
                    rfl

theorem cell23_6158101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 6].length) (baseStart_6158101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158101 prefixEnd_6158101 := by exact prefixLift 6158101
  have htrace : WordTrace (prefixWord ++ tailWord_6158101) baseStart_6158101 baseEnd_6158101 := by
    simpa [prefixWord, tailWord_6158101, baseEnd_6158101] using wordTrace_append hprefix tailTrace_6158101
  have hstable : (prefixWord ++ tailWord_6158101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158101).length < 2 ^ (prefixWord ++ tailWord_6158101).sum := by decide
  have hdescent : baseEnd_6158101 < baseStart_6158101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158107 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 7]
def baseStart_6158107 : Nat := 118140960795 + 6158107 * 2 ^ 59
def prefixEnd_6158107 : Nat := 4983230072969 + 3 ^ 40 * 6158107 * 2
def baseEnd_6158107 : Nat := 3162068812817043111741887

theorem tailTrace_6158107 : CollatzResearch.WordTrace tailWord_6158107 prefixEnd_6158107 3162068812817043111741887 := by
  unfold tailWord_6158107
  simp only [CollatzResearch.WordTrace]
  refine ⟨224604614301237534788928575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149736409534158356525952383 224604614301237534788928575)
  ·
    refine ⟨336906921451856302183392863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224604614301237534788928575 336906921451856302183392863)
    ·
      refine ⟨505360382177784453275089295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336906921451856302183392863 505360382177784453275089295)
      ·
        refine ⟨758040573266676679912633943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505360382177784453275089295 758040573266676679912633943)
        ·
          refine ⟨1137060859900015019868950915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758040573266676679912633943 1137060859900015019868950915)
          ·
            refine ⟨1705591289850022529803426373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137060859900015019868950915 1705591289850022529803426373)
            ·
              refine ⟨319798366846879224338142445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1705591289850022529803426373 319798366846879224338142445)
              ·
                refine ⟨119924387567579709126803417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319798366846879224338142445 119924387567579709126803417)
                ·
                  refine ⟨89943290675684781845102563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119924387567579709126803417 89943290675684781845102563)
                  ·
                    refine ⟨134914936013527172767653845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89943290675684781845102563 134914936013527172767653845)
                    ·
                      refine ⟨3162068812817043111741887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134914936013527172767653845 3162068812817043111741887)
                      ·
                        rfl

theorem cell23_6158107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_6158107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158107 prefixEnd_6158107 := by exact prefixLift 6158107
  have htrace : WordTrace (prefixWord ++ tailWord_6158107) baseStart_6158107 baseEnd_6158107 := by
    simpa [prefixWord, tailWord_6158107, baseEnd_6158107] using wordTrace_append hprefix tailTrace_6158107
  have hstable : (prefixWord ++ tailWord_6158107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158107).length < 2 ^ (prefixWord ++ tailWord_6158107).sum := by decide
  have hdescent : baseEnd_6158107 < baseStart_6158107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158111 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 5, 1, 3]
def baseStart_6158111 : Nat := 118140960795 + 6158111 * 2 ^ 59
def prefixEnd_6158111 : Nat := 4983230072969 + 3 ^ 40 * 6158111 * 2
def baseEnd_6158111 : Nat := 3162070866739661096091869

theorem tailTrace_6158111 : CollatzResearch.WordTrace tailWord_6158111 prefixEnd_6158111 3162070866739661096091869 := by
  unfold tailWord_6158111
  simp only [CollatzResearch.WordTrace]
  refine ⟨224604760193223043472074187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149736506795482028981382791 224604760193223043472074187)
  ·
    refine ⟨336907140289834565208111281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224604760193223043472074187 336907140289834565208111281)
    ·
      refine ⟨252680355217375923906083461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336907140289834565208111281 252680355217375923906083461)
      ·
        refine ⟨47377566603257985732390649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252680355217375923906083461 47377566603257985732390649)
        ·
          refine ⟨35533174952443489299292987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47377566603257985732390649 35533174952443489299292987)
          ·
            refine ⟨53299762428665233948939481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35533174952443489299292987 53299762428665233948939481)
            ·
              refine ⟨39974821821498925461704611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53299762428665233948939481 39974821821498925461704611)
              ·
                refine ⟨59962232732248388192556917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39974821821498925461704611 59962232732248388192556917)
                ·
                  refine ⟨5621459318648286393052211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59962232732248388192556917 5621459318648286393052211)
                  ·
                    refine ⟨8432188977972429589578317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5621459318648286393052211 8432188977972429589578317)
                    ·
                      refine ⟨3162070866739661096091869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8432188977972429589578317 3162070866739661096091869)
                      ·
                        rfl

theorem cell23_6158111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_6158111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158111 prefixEnd_6158111 := by exact prefixLift 6158111
  have htrace : WordTrace (prefixWord ++ tailWord_6158111) baseStart_6158111 baseEnd_6158111 := by
    simpa [prefixWord, tailWord_6158111, baseEnd_6158111] using wordTrace_append hprefix tailTrace_6158111
  have hstable : (prefixWord ++ tailWord_6158111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158111).length < 2 ^ (prefixWord ++ tailWord_6158111).sum := by decide
  have hdescent : baseEnd_6158111 < baseStart_6158111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158138 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2]
def baseStart_6158138 : Nat := 118140960795 + 6158138 * 2 ^ 59
def prefixEnd_6158138 : Nat := 4983230072969 + 3 ^ 40 * 6158138 * 2
def baseEnd_6158138 : Nat := 3162084730717332490454245

theorem tailTrace_6158138 : CollatzResearch.WordTrace tailWord_6158138 prefixEnd_6158138 3162084730717332490454245 := by
  unfold tailWord_6158138
  simp only [CollatzResearch.WordTrace]
  refine ⟨56151436241031306770826767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149737163309416818055538045 56151436241031306770826767)
  ·
    refine ⟨84227154361546960156240151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56151436241031306770826767 84227154361546960156240151)
    ·
      refine ⟨126340731542320440234360227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84227154361546960156240151 126340731542320440234360227)
      ·
        refine ⟨189511097313480660351540341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126340731542320440234360227 189511097313480660351540341)
        ·
          refine ⟨17766665373138811907956907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189511097313480660351540341 17766665373138811907956907)
          ·
            refine ⟨26649998059708217861935361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17766665373138811907956907 26649998059708217861935361)
            ·
              refine ⟨19987498544781163396451521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26649998059708217861935361 19987498544781163396451521)
              ·
                refine ⟨14990623908585872547338641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19987498544781163396451521 14990623908585872547338641)
                ·
                  refine ⟨11242967931439404410503981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14990623908585872547338641 11242967931439404410503981)
                  ·
                    refine ⟨4216112974289776653938993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11242967931439404410503981 4216112974289776653938993)
                    ·
                      refine ⟨3162084730717332490454245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216112974289776653938993 3162084730717332490454245)
                      ·
                        rfl

theorem cell23_6158138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2].length) (baseStart_6158138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158138 prefixEnd_6158138 := by exact prefixLift 6158138
  have htrace : WordTrace (prefixWord ++ tailWord_6158138) baseStart_6158138 baseEnd_6158138 := by
    simpa [prefixWord, tailWord_6158138, baseEnd_6158138] using wordTrace_append hprefix tailTrace_6158138
  have hstable : (prefixWord ++ tailWord_6158138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158138).length < 2 ^ (prefixWord ++ tailWord_6158138).sum := by decide
  have hdescent : baseEnd_6158138 < baseStart_6158138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158154 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_6158154 : Nat := 118140960795 + 6158154 * 2 ^ 59
def prefixEnd_6158154 : Nat := 4983230072969 + 3 ^ 40 * 6158154 * 2
def baseEnd_6158154 : Nat := 3162092946407804427854171

theorem tailTrace_6158154 : CollatzResearch.WordTrace tailWord_6158154 prefixEnd_6158154 3162092946407804427854171 := by
  unfold tailWord_6158154
  simp only [CollatzResearch.WordTrace]
  refine ⟨56151582133016815453972379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149737552354711507877259677 56151582133016815453972379)
  ·
    refine ⟨84227373199525223180958569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56151582133016815453972379 84227373199525223180958569)
    ·
      refine ⟨63170529899643917385718927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84227373199525223180958569 63170529899643917385718927)
      ·
        refine ⟨94755794849465876078578391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63170529899643917385718927 94755794849465876078578391)
        ·
          refine ⟨142133692274198814117867587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94755794849465876078578391 142133692274198814117867587)
          ·
            refine ⟨213200538411298221176801381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142133692274198814117867587 213200538411298221176801381)
            ·
              refine ⟨39975100952118416470650259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213200538411298221176801381 39975100952118416470650259)
              ·
                refine ⟨59962651428177624705975389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39975100952118416470650259 59962651428177624705975389)
                ·
                  refine ⟨22485994285566609264740771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59962651428177624705975389 22485994285566609264740771)
                  ·
                    refine ⟨33728991428349913897111157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22485994285566609264740771 33728991428349913897111157)
                    ·
                      refine ⟨3162092946407804427854171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33728991428349913897111157 3162092946407804427854171)
                      ·
                        rfl

theorem cell23_6158154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_6158154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158154 prefixEnd_6158154 := by exact prefixLift 6158154
  have htrace : WordTrace (prefixWord ++ tailWord_6158154) baseStart_6158154 baseEnd_6158154 := by
    simpa [prefixWord, tailWord_6158154, baseEnd_6158154] using wordTrace_append hprefix tailTrace_6158154
  have hstable : (prefixWord ++ tailWord_6158154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158154).length < 2 ^ (prefixWord ++ tailWord_6158154).sum := by decide
  have hdescent : baseEnd_6158154 < baseStart_6158154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158161 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 1, 6]
def baseStart_6158161 : Nat := 118140960795 + 6158161 * 2 ^ 59
def prefixEnd_6158161 : Nat := 4983230072969 + 3 ^ 40 * 6158161 * 2
def baseEnd_6158161 : Nat := 1054032180257461966822213

theorem tailTrace_6158161 : CollatzResearch.WordTrace tailWord_6158161 prefixEnd_6158161 1054032180257461966822213 := by
  unfold tailWord_6158161
  simp only [CollatzResearch.WordTrace]
  refine ⟨224606583843041902011394337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149737722562027934674262891 224606583843041902011394337)
  ·
    refine ⟨168454937882281426508545753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224606583843041902011394337 168454937882281426508545753)
    ·
      refine ⟨126341203411711069881409315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168454937882281426508545753 126341203411711069881409315)
      ·
        refine ⟨189511805117566604822113973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126341203411711069881409315 189511805117566604822113973)
        ·
          refine ⟨17766731729771869202073185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189511805117566604822113973 17766731729771869202073185)
          ·
            refine ⟨13325048797328901901554889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17766731729771869202073185 13325048797328901901554889)
            ·
              refine ⟨9993786597996676426166167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13325048797328901901554889 9993786597996676426166167)
              ·
                refine ⟨14990679896995014639249251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9993786597996676426166167 14990679896995014639249251)
                ·
                  refine ⟨22486019845492521958873877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14990679896995014639249251 22486019845492521958873877)
                  ·
                    refine ⟨1054032180257461966822213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22486019845492521958873877 1054032180257461966822213)
                    ·
                      rfl

theorem cell23_6158161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_6158161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158161 prefixEnd_6158161 := by exact prefixLift 6158161
  have htrace : WordTrace (prefixWord ++ tailWord_6158161) baseStart_6158161 baseEnd_6158161 := by
    simpa [prefixWord, tailWord_6158161, baseEnd_6158161] using wordTrace_append hprefix tailTrace_6158161
  have hstable : (prefixWord ++ tailWord_6158161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158161).length < 2 ^ (prefixWord ++ tailWord_6158161).sum := by decide
  have hdescent : baseEnd_6158161 < baseStart_6158161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158172 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_6158172 : Nat := 118140960795 + 6158172 * 2 ^ 59
def prefixEnd_6158172 : Nat := 4983230072969 + 3 ^ 40 * 6158172 * 2
def baseEnd_6158172 : Nat := 3162102189059585357429089

theorem tailTrace_6158172 : CollatzResearch.WordTrace tailWord_6158172 prefixEnd_6158172 3162102189059585357429089 := by
  unfold tailWord_6158172
  simp only [CollatzResearch.WordTrace]
  refine ⟨112303492523001025445022385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149737990030668033926696513 112303492523001025445022385)
  ·
    refine ⟨84227619392250769083766789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112303492523001025445022385 84227619392250769083766789)
    ·
      refine ⟨15792678636047019203206273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84227619392250769083766789 15792678636047019203206273)
      ·
        refine ⟨11844508977035264402404705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15792678636047019203206273 11844508977035264402404705)
        ·
          refine ⟨8883381732776448301803529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11844508977035264402404705 8883381732776448301803529)
          ·
            refine ⟨6662536299582336226352647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8883381732776448301803529 6662536299582336226352647)
            ·
              refine ⟨9993804449373504339528971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6662536299582336226352647 9993804449373504339528971)
              ·
                refine ⟨14990706674060256509293457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9993804449373504339528971 14990706674060256509293457)
                ·
                  refine ⟨11243030005545192381970093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14990706674060256509293457 11243030005545192381970093)
                  ·
                    refine ⟨4216136252079447143238785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11243030005545192381970093 4216136252079447143238785)
                    ·
                      refine ⟨3162102189059585357429089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216136252079447143238785 3162102189059585357429089)
                      ·
                        rfl

theorem cell23_6158172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_6158172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158172 prefixEnd_6158172 := by exact prefixLift 6158172
  have htrace : WordTrace (prefixWord ++ tailWord_6158172) baseStart_6158172 baseEnd_6158172 := by
    simpa [prefixWord, tailWord_6158172, baseEnd_6158172] using wordTrace_append hprefix tailTrace_6158172
  have hstable : (prefixWord ++ tailWord_6158172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158172).length < 2 ^ (prefixWord ++ tailWord_6158172).sum := by decide
  have hdescent : baseEnd_6158172 < baseStart_6158172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158188 : List Nat := [2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 3]
def baseStart_6158188 : Nat := 118140960795 + 6158188 * 2 ^ 59
def prefixEnd_6158188 : Nat := 4983230072969 + 3 ^ 40 * 6158188 * 2
def baseEnd_6158188 : Nat := 3162110404750057294829015

theorem tailTrace_6158188 : CollatzResearch.WordTrace tailWord_6158188 prefixEnd_6158188 3162110404750057294829015 := by
  unfold tailWord_6158188
  simp only [CollatzResearch.WordTrace]
  refine ⟨112303784306972042811313609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149738379075962723748418145 112303784306972042811313609)
  ·
    refine ⟨84227838230229032108485207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112303784306972042811313609 84227838230229032108485207)
    ·
      refine ⟨126341757345343548162727811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84227838230229032108485207 126341757345343548162727811)
      ·
        refine ⟨189512636018015322244091717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126341757345343548162727811 189512636018015322244091717)
        ·
          refine ⟨35533619253377872920767197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189512636018015322244091717 35533619253377872920767197)
          ·
            refine ⟨13325107220016702345287699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35533619253377872920767197 13325107220016702345287699)
            ·
              refine ⟨19987660830025053517931549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13325107220016702345287699 19987660830025053517931549)
              ·
                refine ⟨7495372811259395069224331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19987660830025053517931549 7495372811259395069224331)
                ·
                  refine ⟨11243059216889092603836497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7495372811259395069224331 11243059216889092603836497)
                  ·
                    refine ⟨8432294412666819452877373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11243059216889092603836497 8432294412666819452877373)
                    ·
                      refine ⟨3162110404750057294829015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8432294412666819452877373 3162110404750057294829015)
                      ·
                        rfl

theorem cell23_6158188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_6158188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158188 prefixEnd_6158188 := by exact prefixLift 6158188
  have htrace : WordTrace (prefixWord ++ tailWord_6158188) baseStart_6158188 baseEnd_6158188 := by
    simpa [prefixWord, tailWord_6158188, baseEnd_6158188] using wordTrace_append hprefix tailTrace_6158188
  have hstable : (prefixWord ++ tailWord_6158188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158188).length < 2 ^ (prefixWord ++ tailWord_6158188).sum := by decide
  have hdescent : baseEnd_6158188 < baseStart_6158188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158194 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_6158194 : Nat := 118140960795 + 6158194 * 2 ^ 59
def prefixEnd_6158194 : Nat := 4983230072969 + 3 ^ 40 * 6158194 * 2
def baseEnd_6158194 : Nat := 3162113485633984271353987

theorem tailTrace_6158194 : CollatzResearch.WordTrace tailWord_6158194 prefixEnd_6158194 3162113485633984271353987 := by
  unfold tailWord_6158194
  simp only [CollatzResearch.WordTrace]
  refine ⟨56151946862980587161836409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149738524967948232431563757 56151946862980587161836409)
  ·
    refine ⟨42113960147235440371377307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56151946862980587161836409 42113960147235440371377307)
    ·
      refine ⟨63170940220853160557065961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42113960147235440371377307 63170940220853160557065961)
      ·
        refine ⟨47378205165639870417799471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63170940220853160557065961 47378205165639870417799471)
        ·
          refine ⟨71067307748459805626699207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47378205165639870417799471 71067307748459805626699207)
          ·
            refine ⟨106600961622689708440048811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71067307748459805626699207 106600961622689708440048811)
            ·
              refine ⟨159901442434034562660073217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106600961622689708440048811 159901442434034562660073217)
              ·
                refine ⟨119926081825525921995054913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159901442434034562660073217 119926081825525921995054913)
                ·
                  refine ⟨89944561369144441496291185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119926081825525921995054913 89944561369144441496291185)
                  ·
                    refine ⟨67458421026858331122218389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89944561369144441496291185 67458421026858331122218389)
                    ·
                      refine ⟨3162113485633984271353987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67458421026858331122218389 3162113485633984271353987)
                      ·
                        rfl

theorem cell23_6158194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_6158194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158194 prefixEnd_6158194 := by exact prefixLift 6158194
  have htrace : WordTrace (prefixWord ++ tailWord_6158194) baseStart_6158194 baseEnd_6158194 := by
    simpa [prefixWord, tailWord_6158194, baseEnd_6158194] using wordTrace_append hprefix tailTrace_6158194
  have hstable : (prefixWord ++ tailWord_6158194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158194).length < 2 ^ (prefixWord ++ tailWord_6158194).sum := by decide
  have hdescent : baseEnd_6158194 < baseStart_6158194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158215 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 1, 2, 4]
def baseStart_6158215 : Nat := 118140960795 + 6158215 * 2 ^ 59
def prefixEnd_6158215 : Nat := 4983230072969 + 3 ^ 40 * 6158215 * 2
def baseEnd_6158215 : Nat := 3162124268727728689191391

theorem tailTrace_6158215 : CollatzResearch.WordTrace tailWord_6158215 prefixEnd_6158215 3162124268727728689191391 := by
  unfold tailWord_6158215
  simp only [CollatzResearch.WordTrace]
  refine ⟨224608553384846269233860099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149739035589897512822573399 224608553384846269233860099)
  ·
    refine ⟨336912830077269403850790149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224608553384846269233860099 336912830077269403850790149)
    ·
      refine ⟨63171155639488013222023153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336912830077269403850790149 63171155639488013222023153)
      ·
        refine ⟨47378366729616009916517365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63171155639488013222023153 47378366729616009916517365)
        ·
          refine ⟨4441721880901500929673503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47378366729616009916517365 4441721880901500929673503)
          ·
            refine ⟨6662582821352251394510255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4441721880901500929673503 6662582821352251394510255)
            ·
              refine ⟨9993874232028377091765383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6662582821352251394510255 9993874232028377091765383)
              ·
                refine ⟨14990811348042565637648075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9993874232028377091765383 14990811348042565637648075)
                ·
                  refine ⟨22486217022063848456472113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14990811348042565637648075 22486217022063848456472113)
                  ·
                    refine ⟨16864662766547886342354085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22486217022063848456472113 16864662766547886342354085)
                    ·
                      refine ⟨3162124268727728689191391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16864662766547886342354085 3162124268727728689191391)
                      ·
                        rfl

theorem cell23_6158215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_6158215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158215 prefixEnd_6158215 := by exact prefixLift 6158215
  have htrace : WordTrace (prefixWord ++ tailWord_6158215) baseStart_6158215 baseEnd_6158215 := by
    simpa [prefixWord, tailWord_6158215, baseEnd_6158215] using wordTrace_append hprefix tailTrace_6158215
  have hstable : (prefixWord ++ tailWord_6158215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158215).length < 2 ^ (prefixWord ++ tailWord_6158215).sum := by decide
  have hdescent : baseEnd_6158215 < baseStart_6158215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158222 : List Nat := [4, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6158222 : Nat := 118140960795 + 6158222 * 2 ^ 59
def prefixEnd_6158222 : Nat := 4983230072969 + 3 ^ 40 * 6158222 * 2
def baseEnd_6158222 : Nat := 3162127863092310161803859

theorem tailTrace_6158222 : CollatzResearch.WordTrace tailWord_6158222 prefixEnd_6158222 3162127863092310161803859 := by
  unfold tailWord_6158222
  simp only [CollatzResearch.WordTrace]
  refine ⟨28076101086977613678670615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149739205797213939619576613 28076101086977613678670615)
  ·
    refine ⟨42114151630466420518005923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28076101086977613678670615 42114151630466420518005923)
    ·
      refine ⟨63171227445699630777008885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42114151630466420518005923 63171227445699630777008885)
      ·
        refine ⟨5922302573034340385344583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63171227445699630777008885 5922302573034340385344583)
        ·
          refine ⟨8883453859551510578016875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5922302573034340385344583 8883453859551510578016875)
          ·
            refine ⟨13325180789327265867025313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8883453859551510578016875 13325180789327265867025313)
            ·
              refine ⟨9993885591995449400268985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13325180789327265867025313 9993885591995449400268985)
              ·
                refine ⟨7495414193996587050201739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9993885591995449400268985 7495414193996587050201739)
                ·
                  refine ⟨11243121290994880575302609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7495414193996587050201739 11243121290994880575302609)
                  ·
                    refine ⟨8432340968246160431476957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11243121290994880575302609 8432340968246160431476957)
                    ·
                      refine ⟨3162127863092310161803859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8432340968246160431476957 3162127863092310161803859)
                      ·
                        rfl

theorem cell23_6158222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6158222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158222 prefixEnd_6158222 := by exact prefixLift 6158222
  have htrace : WordTrace (prefixWord ++ tailWord_6158222) baseStart_6158222 baseEnd_6158222 := by
    simpa [prefixWord, tailWord_6158222, baseEnd_6158222] using wordTrace_append hprefix tailTrace_6158222
  have hstable : (prefixWord ++ tailWord_6158222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158222).length < 2 ^ (prefixWord ++ tailWord_6158222).sum := by decide
  have hdescent : baseEnd_6158222 < baseStart_6158222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158224 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 4]
def baseStart_6158224 : Nat := 118140960795 + 6158224 * 2 ^ 59
def prefixEnd_6158224 : Nat := 4983230072969 + 3 ^ 40 * 6158224 * 2
def baseEnd_6158224 : Nat := 3162128890053619153978849

theorem tailTrace_6158224 : CollatzResearch.WordTrace tailWord_6158224 prefixEnd_6158224 3162128890053619153978849 := by
  unfold tailWord_6158224
  simp only [CollatzResearch.WordTrace]
  refine ⟨112304440820906831885468863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149739254427875775847291817 112304440820906831885468863)
  ·
    refine ⟨168456661231360247828203295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112304440820906831885468863 168456661231360247828203295)
    ·
      refine ⟨252684991847040371742304943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168456661231360247828203295 252684991847040371742304943)
      ·
        refine ⟨379027487770560557613457415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252684991847040371742304943 379027487770560557613457415)
        ·
          refine ⟨568541231655840836420186123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379027487770560557613457415 568541231655840836420186123)
          ·
            refine ⟨852811847483761254630279185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568541231655840836420186123 852811847483761254630279185)
            ·
              refine ⟨639608885612820940972709389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 852811847483761254630279185 639608885612820940972709389)
              ·
                refine ⟨239853332104807852864766021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 639608885612820940972709389 239853332104807852864766021)
                ·
                  refine ⟨44972499769651472412143629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 239853332104807852864766021 44972499769651472412143629)
                  ·
                    refine ⟨16864687413619302154553861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44972499769651472412143629 16864687413619302154553861)
                    ·
                      refine ⟨3162128890053619153978849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16864687413619302154553861 3162128890053619153978849)
                      ·
                        rfl

theorem cell23_6158224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_6158224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158224 prefixEnd_6158224 := by exact prefixLift 6158224
  have htrace : WordTrace (prefixWord ++ tailWord_6158224) baseStart_6158224 baseEnd_6158224 := by
    simpa [prefixWord, tailWord_6158224, baseEnd_6158224] using wordTrace_append hprefix tailTrace_6158224
  have hstable : (prefixWord ++ tailWord_6158224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158224).length < 2 ^ (prefixWord ++ tailWord_6158224).sum := by decide
  have hdescent : baseEnd_6158224 < baseStart_6158224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158331 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 4]
def baseStart_6158331 : Nat := 118140960795 + 6158331 * 2 ^ 59
def prefixEnd_6158331 : Nat := 4983230072969 + 3 ^ 40 * 6158331 * 2
def baseEnd_6158331 : Nat := 3162183832483650235340857

theorem tailTrace_6158331 : CollatzResearch.WordTrace tailWord_6158331 prefixEnd_6158331 3162183832483650235340857 := by
  unfold tailWord_6158331
  simp only [CollatzResearch.WordTrace]
  refine ⟨224612784252426021045082847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149741856168284014030055231 224612784252426021045082847)
  ·
    refine ⟨336919176378639031567624271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224612784252426021045082847 336919176378639031567624271)
    ·
      refine ⟨505378764567958547351436407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336919176378639031567624271 505378764567958547351436407)
      ·
        refine ⟨758068146851937821027154611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505378764567958547351436407 758068146851937821027154611)
        ·
          refine ⟨1137102220277906731540731917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758068146851937821027154611 1137102220277906731540731917)
          ·
            refine ⟨426413332604215024327774469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1137102220277906731540731917 426413332604215024327774469)
            ·
              refine ⟨79952499863290317061457713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 426413332604215024327774469 79952499863290317061457713)
              ·
                refine ⟨59964374897467737796093285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79952499863290317061457713 59964374897467737796093285)
                ·
                  refine ⟨11243320293275200836767491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59964374897467737796093285 11243320293275200836767491)
                  ·
                    refine ⟨16864980439912801255151237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11243320293275200836767491 16864980439912801255151237)
                    ·
                      refine ⟨3162183832483650235340857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16864980439912801255151237 3162183832483650235340857)
                      ·
                        rfl

theorem cell23_6158331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 4].length) (baseStart_6158331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158331 prefixEnd_6158331 := by exact prefixLift 6158331
  have htrace : WordTrace (prefixWord ++ tailWord_6158331) baseStart_6158331 baseEnd_6158331 := by
    simpa [prefixWord, tailWord_6158331, baseEnd_6158331] using wordTrace_append hprefix tailTrace_6158331
  have hstable : (prefixWord ++ tailWord_6158331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158331).length < 2 ^ (prefixWord ++ tailWord_6158331).sum := by decide
  have hdescent : baseEnd_6158331 < baseStart_6158331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158348 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 1, 6, 2]
def baseStart_6158348 : Nat := 118140960795 + 6158348 * 2 ^ 59
def prefixEnd_6158348 : Nat := 4983230072969 + 3 ^ 40 * 6158348 * 2
def baseEnd_6158348 : Nat := 3162192561654776668828279

theorem tailTrace_6158348 : CollatzResearch.WordTrace tailWord_6158348 prefixEnd_6158348 3162192561654776668828279 := by
  unfold tailWord_6158348
  simp only [CollatzResearch.WordTrace]
  refine ⟨112306702146682216474225849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149742269528909621965634465 112306702146682216474225849)
  ·
    refine ⟨84230026610011662355669387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112306702146682216474225849 84230026610011662355669387)
    ·
      refine ⟨126345039915017493533504081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84230026610011662355669387 126345039915017493533504081)
      ·
        refine ⟨94758779936263120150128061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126345039915017493533504081 94758779936263120150128061)
        ·
          refine ⟨35534542476098670056298023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94758779936263120150128061 35534542476098670056298023)
          ·
            refine ⟨53301813714148005084447035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35534542476098670056298023 53301813714148005084447035)
            ·
              refine ⟨79952720571222007626670553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53301813714148005084447035 79952720571222007626670553)
              ·
                refine ⟨59964540428416505720002915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79952720571222007626670553 59964540428416505720002915)
                ·
                  refine ⟨89946810642624758580004373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59964540428416505720002915 89946810642624758580004373)
                  ·
                    refine ⟨4216256748873035558437705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89946810642624758580004373 4216256748873035558437705)
                    ·
                      refine ⟨3162192561654776668828279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216256748873035558437705 3162192561654776668828279)
                      ·
                        rfl

theorem cell23_6158348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_6158348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158348 prefixEnd_6158348 := by exact prefixLift 6158348
  have htrace : WordTrace (prefixWord ++ tailWord_6158348) baseStart_6158348 baseEnd_6158348 := by
    simpa [prefixWord, tailWord_6158348, baseEnd_6158348] using wordTrace_append hprefix tailTrace_6158348
  have hstable : (prefixWord ++ tailWord_6158348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158348).length < 2 ^ (prefixWord ++ tailWord_6158348).sum := by decide
  have hdescent : baseEnd_6158348 < baseStart_6158348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158365 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_6158365 : Nat := 118140960795 + 6158365 * 2 ^ 59
def prefixEnd_6158365 : Nat := 4983230072969 + 3 ^ 40 * 6158365 * 2
def baseEnd_6158365 : Nat := 3162201290825903102315701

theorem tailTrace_6158365 : CollatzResearch.WordTrace tailWord_6158365 prefixEnd_6158365 3162201290825903102315701 := by
  unfold tailWord_6158365
  simp only [CollatzResearch.WordTrace]
  refine ⟨224614024334302844851820549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149742682889535229901213699 224614024334302844851820549)
  ·
    refine ⟨42115129562681783409716353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224614024334302844851820549 42115129562681783409716353)
    ·
      refine ⟨31586347172011337557287265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42115129562681783409716353 31586347172011337557287265)
      ·
        refine ⟨23689760379008503167965449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31586347172011337557287265 23689760379008503167965449)
        ·
          refine ⟨17767320284256377375974087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23689760379008503167965449 17767320284256377375974087)
          ·
            refine ⟨26650980426384566063961131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17767320284256377375974087 26650980426384566063961131)
            ·
              refine ⟨39976470639576849095941697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26650980426384566063961131 39976470639576849095941697)
              ·
                refine ⟨29982352979682636821956273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39976470639576849095941697 29982352979682636821956273)
                ·
                  refine ⟨22486764734761977616467205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29982352979682636821956273 22486764734761977616467205)
                  ·
                    refine ⟨4216268387767870803087601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22486764734761977616467205 4216268387767870803087601)
                    ·
                      refine ⟨3162201290825903102315701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216268387767870803087601 3162201290825903102315701)
                      ·
                        rfl

theorem cell23_6158365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_6158365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158365 prefixEnd_6158365 := by exact prefixLift 6158365
  have htrace : WordTrace (prefixWord ++ tailWord_6158365) baseStart_6158365 baseEnd_6158365 := by
    simpa [prefixWord, tailWord_6158365, baseEnd_6158365] using wordTrace_append hprefix tailTrace_6158365
  have hstable : (prefixWord ++ tailWord_6158365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158365).length < 2 ^ (prefixWord ++ tailWord_6158365).sum := by decide
  have hdescent : baseEnd_6158365 < baseStart_6158365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158371 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 8]
def baseStart_6158371 : Nat := 118140960795 + 6158371 * 2 ^ 59
def prefixEnd_6158371 : Nat := 4983230072969 + 3 ^ 40 * 6158371 * 2
def baseEnd_6158371 : Nat := 351356041301092230982297

theorem tailTrace_6158371 : CollatzResearch.WordTrace tailWord_6158371 prefixEnd_6158371 351356041301092230982297 := by
  unfold tailWord_6158371
  simp only [CollatzResearch.WordTrace]
  refine ⟨224614243172281107876538967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149742828781520738584359311 224614243172281107876538967)
  ·
    refine ⟨336921364758421661814808451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224614243172281107876538967 336921364758421661814808451)
    ·
      refine ⟨505382047137632492722212677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336921364758421661814808451 505382047137632492722212677)
      ·
        refine ⟨94759133838306092385414877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 505382047137632492722212677 94759133838306092385414877)
        ·
          refine ⟨35534675189364784644530579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94759133838306092385414877 35534675189364784644530579)
          ·
            refine ⟨53302012784047176966795869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35534675189364784644530579 53302012784047176966795869)
            ·
              refine ⟨19988254794017691362548451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53302012784047176966795869 19988254794017691362548451)
              ·
                refine ⟨29982382191026537043822677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19988254794017691362548451 29982382191026537043822677)
                ·
                  refine ⟨351356041301092230982297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29982382191026537043822677 351356041301092230982297)
                  ·
                    rfl

theorem cell23_6158371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 8].length) (baseStart_6158371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158371 prefixEnd_6158371 := by exact prefixLift 6158371
  have htrace : WordTrace (prefixWord ++ tailWord_6158371) baseStart_6158371 baseEnd_6158371 := by
    simpa [prefixWord, tailWord_6158371, baseEnd_6158371] using wordTrace_append hprefix tailTrace_6158371
  have hstable : (prefixWord ++ tailWord_6158371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158371).length < 2 ^ (prefixWord ++ tailWord_6158371).sum := by decide
  have hdescent : baseEnd_6158371 < baseStart_6158371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158425 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 2, 3, 2]
def baseStart_6158425 : Nat := 118140960795 + 6158425 * 2 ^ 59
def prefixEnd_6158425 : Nat := 4983230072969 + 3 ^ 40 * 6158425 * 2
def baseEnd_6158425 : Nat := 3162232099665172867565425

theorem tailTrace_6158425 : CollatzResearch.WordTrace tailWord_6158425 prefixEnd_6158425 3162232099665172867565425 := by
  unfold tailWord_6158425
  simp only [CollatzResearch.WordTrace]
  refine ⟨224616212714085475099004729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149744141809390316732669819 224616212714085475099004729)
  ·
    refine ⟨168462159535564106324253547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224616212714085475099004729 168462159535564106324253547)
    ·
      refine ⟨252693239303346159486380321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168462159535564106324253547 252693239303346159486380321)
      ·
        refine ⟨189519929477509619614785241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252693239303346159486380321 189519929477509619614785241)
        ·
          refine ⟨142139947108132214711088931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189519929477509619614785241 142139947108132214711088931)
          ·
            refine ⟨213209920662198322066633397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142139947108132214711088931 213209920662198322066633397)
            ·
              refine ⟨19988430062081092693746881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213209920662198322066633397 19988430062081092693746881)
              ·
                refine ⟨14991322546560819520310161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19988430062081092693746881 14991322546560819520310161)
                ·
                  refine ⟨11243491909920614640232621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14991322546560819520310161 11243491909920614640232621)
                  ·
                    refine ⟨4216309466220230490087233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11243491909920614640232621 4216309466220230490087233)
                    ·
                      refine ⟨3162232099665172867565425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216309466220230490087233 3162232099665172867565425)
                      ·
                        rfl

theorem cell23_6158425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 3, 2].length) (baseStart_6158425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158425 prefixEnd_6158425 := by exact prefixLift 6158425
  have htrace : WordTrace (prefixWord ++ tailWord_6158425) baseStart_6158425 baseEnd_6158425 := by
    simpa [prefixWord, tailWord_6158425, baseEnd_6158425] using wordTrace_append hprefix tailTrace_6158425
  have hstable : (prefixWord ++ tailWord_6158425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158425).length < 2 ^ (prefixWord ++ tailWord_6158425).sum := by decide
  have hdescent : baseEnd_6158425 < baseStart_6158425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158431 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 5, 6]
def baseStart_6158431 : Nat := 118140960795 + 6158431 * 2 ^ 59
def prefixEnd_6158431 : Nat := 4983230072969 + 3 ^ 40 * 6158431 * 2
def baseEnd_6158431 : Nat := 1054078393516366614696799

theorem tailTrace_6158431 : CollatzResearch.WordTrace tailWord_6158431 prefixEnd_6158431 1054078393516366614696799 := by
  unfold tailWord_6158431
  simp only [CollatzResearch.WordTrace]
  refine ⟨224616431552063738123723147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149744287701375825415815431 224616431552063738123723147)
  ·
    refine ⟨336924647328095607185584721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224616431552063738123723147 336924647328095607185584721)
    ·
      refine ⟨252693485496071705389188541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336924647328095607185584721 252693485496071705389188541)
      ·
        refine ⟨94760057061026889520945703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252693485496071705389188541 94760057061026889520945703)
        ·
          refine ⟨142140085591540334281418555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94760057061026889520945703 142140085591540334281418555)
          ·
            refine ⟨213210128387310501422127833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142140085591540334281418555 213210128387310501422127833)
            ·
              refine ⟨159907596290482876066595875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213210128387310501422127833 159907596290482876066595875)
              ·
                refine ⟨239861394435724314099893813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159907596290482876066595875 239861394435724314099893813)
                ·
                  refine ⟨22487005728349154446865045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239861394435724314099893813 22487005728349154446865045)
                  ·
                    refine ⟨1054078393516366614696799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22487005728349154446865045 1054078393516366614696799)
                    ·
                      rfl

theorem cell23_6158431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_6158431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158431 prefixEnd_6158431 := by exact prefixLift 6158431
  have htrace : WordTrace (prefixWord ++ tailWord_6158431) baseStart_6158431 baseEnd_6158431 := by
    simpa [prefixWord, tailWord_6158431, baseEnd_6158431] using wordTrace_append hprefix tailTrace_6158431
  have hstable : (prefixWord ++ tailWord_6158431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158431).length < 2 ^ (prefixWord ++ tailWord_6158431).sum := by decide
  have hdescent : baseEnd_6158431 < baseStart_6158431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158432 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 3, 1, 3]
def baseStart_6158432 : Nat := 118140960795 + 6158432 * 2 ^ 59
def prefixEnd_6158432 : Nat := 4983230072969 + 3 ^ 40 * 6158432 * 2
def baseEnd_6158432 : Nat := 3162235694029754340177893

theorem tailTrace_6158432 : CollatzResearch.WordTrace tailWord_6158432 prefixEnd_6158432 3162235694029754340177893 := by
  unfold tailWord_6158432
  simp only [CollatzResearch.WordTrace]
  refine ⟨112308234012530057647254775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149744312016706743529673033 112308234012530057647254775)
  ·
    refine ⟨168462351018795086470882163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112308234012530057647254775 168462351018795086470882163)
    ·
      refine ⟨252693526528192629706323245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168462351018795086470882163 252693526528192629706323245)
      ·
        refine ⟨94760072448072236139871217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252693526528192629706323245 94760072448072236139871217)
        ·
          refine ⟨71070054336054177104903413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94760072448072236139871217 71070054336054177104903413)
          ·
            refine ⟨6662817594005079103584695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71070054336054177104903413 6662817594005079103584695)
            ·
              refine ⟨9994226391007618655377043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6662817594005079103584695 9994226391007618655377043)
              ·
                refine ⟨14991339586511427983065565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9994226391007618655377043 14991339586511427983065565)
                ·
                  refine ⟨5621752344941785493649587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14991339586511427983065565 5621752344941785493649587)
                  ·
                    refine ⟨8432628517412678240474381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5621752344941785493649587 8432628517412678240474381)
                    ·
                      refine ⟨3162235694029754340177893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8432628517412678240474381 3162235694029754340177893)
                      ·
                        rfl

theorem cell23_6158432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_6158432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158432 prefixEnd_6158432 := by exact prefixLift 6158432
  have htrace : WordTrace (prefixWord ++ tailWord_6158432) baseStart_6158432 baseEnd_6158432 := by
    simpa [prefixWord, tailWord_6158432, baseEnd_6158432] using wordTrace_append hprefix tailTrace_6158432
  have hstable : (prefixWord ++ tailWord_6158432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158432).length < 2 ^ (prefixWord ++ tailWord_6158432).sum := by decide
  have hdescent : baseEnd_6158432 < baseStart_6158432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158455 : List Nat := [1, 1, 3, 1, 1, 5, 3, 2, 1, 1, 4]
def baseStart_6158455 : Nat := 118140960795 + 6158455 * 2 ^ 59
def prefixEnd_6158455 : Nat := 4983230072969 + 3 ^ 40 * 6158455 * 2
def baseEnd_6158455 : Nat := 3162247504084807750190287

theorem tailTrace_6158455 : CollatzResearch.WordTrace tailWord_6158455 prefixEnd_6158455 3162247504084807750190287 := by
  unfold tailWord_6158455
  simp only [CollatzResearch.WordTrace]
  refine ⟨224617306903976790222596819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149744871269317860148397879 224617306903976790222596819)
  ·
    refine ⟨336925960355965185333895229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224617306903976790222596819 336925960355965185333895229)
    ·
      refine ⟨126347235133486944500210711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336925960355965185333895229 126347235133486944500210711)
      ·
        refine ⟨189520852700230416750316067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126347235133486944500210711 189520852700230416750316067)
        ·
          refine ⟨284281279050345625125474101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189520852700230416750316067 284281279050345625125474101)
          ·
            refine ⟨26651369910969902355513197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 284281279050345625125474101 26651369910969902355513197)
            ·
              refine ⟨9994263716613713383317449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26651369910969902355513197 9994263716613713383317449)
              ·
                refine ⟨7495697787460285037488087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9994263716613713383317449 7495697787460285037488087)
                ·
                  refine ⟨11243546681190427556232131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7495697787460285037488087 11243546681190427556232131)
                  ·
                    refine ⟨16865320021785641334348197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11243546681190427556232131 16865320021785641334348197)
                    ·
                      refine ⟨3162247504084807750190287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16865320021785641334348197 3162247504084807750190287)
                      ·
                        rfl

theorem cell23_6158455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_6158455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158455 prefixEnd_6158455 := by exact prefixLift 6158455
  have htrace : WordTrace (prefixWord ++ tailWord_6158455) baseStart_6158455 baseEnd_6158455 := by
    simpa [prefixWord, tailWord_6158455, baseEnd_6158455] using wordTrace_append hprefix tailTrace_6158455
  have hstable : (prefixWord ++ tailWord_6158455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158455).length < 2 ^ (prefixWord ++ tailWord_6158455).sum := by decide
  have hdescent : baseEnd_6158455 < baseStart_6158455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158465 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 1, 6]
def baseStart_6158465 : Nat := 118140960795 + 6158465 * 2 ^ 59
def prefixEnd_6158465 : Nat := 4983230072969 + 3 ^ 40 * 6158465 * 2
def baseEnd_6158465 : Nat := 1054084212963784237021747

theorem tailTrace_6158465 : CollatzResearch.WordTrace tailWord_6158465 prefixEnd_6158465 1054084212963784237021747 := by
  unfold tailWord_6158465
  simp only [CollatzResearch.WordTrace]
  refine ⟨224617671633940561930460849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149745114422627041286973899 224617671633940561930460849)
  ·
    refine ⟨168463253725455421447845637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224617671633940561930460849 168463253725455421447845637)
    ·
      refine ⟨31586860073522891521471057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168463253725455421447845637 31586860073522891521471057)
      ·
        refine ⟨23690145055142168641103293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31586860073522891521471057 23690145055142168641103293)
        ·
          refine ⟨8883804395678313240413735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23690145055142168641103293 8883804395678313240413735)
          ·
            refine ⟨13325706593517469860620603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8883804395678313240413735 13325706593517469860620603)
            ·
              refine ⟨19988559890276204790930905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13325706593517469860620603 19988559890276204790930905)
              ·
                refine ⟨14991419917707153593198179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19988559890276204790930905 14991419917707153593198179)
                ·
                  refine ⟨22487129876560730389797269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14991419917707153593198179 22487129876560730389797269)
                  ·
                    refine ⟨1054084212963784237021747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22487129876560730389797269 1054084212963784237021747)
                    ·
                      rfl

theorem cell23_6158465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_6158465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158465 prefixEnd_6158465 := by exact prefixLift 6158465
  have htrace : WordTrace (prefixWord ++ tailWord_6158465) baseStart_6158465 baseEnd_6158465 := by
    simpa [prefixWord, tailWord_6158465, baseEnd_6158465] using wordTrace_append hprefix tailTrace_6158465
  have hstable : (prefixWord ++ tailWord_6158465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158465).length < 2 ^ (prefixWord ++ tailWord_6158465).sum := by decide
  have hdescent : baseEnd_6158465 < baseStart_6158465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158478 : List Nat := [4, 1, 1, 3, 3, 11]
def baseStart_6158478 : Nat := 118140960795 + 6158478 * 2 ^ 59
def prefixEnd_6158478 : Nat := 4983230072969 + 3 ^ 40 * 6158478 * 2
def baseEnd_6158478 : Nat := 13013412815390375144867

theorem tailTrace_6158478 : CollatzResearch.WordTrace tailWord_6158478 prefixEnd_6158478 13013412815390375144867 := by
  unfold tailWord_6158478
  simp only [CollatzResearch.WordTrace]
  refine ⟨28077268222861683143835511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149745430521928976767122725 28077268222861683143835511)
  ·
    refine ⟨42115902334292524715753267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28077268222861683143835511 42115902334292524715753267)
    ·
      refine ⟨63173853501438787073629901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42115902334292524715753267 63173853501438787073629901)
      ·
        refine ⟨23690195063039545152611213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63173853501438787073629901 23690195063039545152611213)
        ·
          refine ⟨8883823148639829432229205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23690195063039545152611213 8883823148639829432229205)
          ·
            refine ⟨13013412815390375144867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8883823148639829432229205 13013412815390375144867)
            ·
              rfl

theorem cell23_6158478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 11].length) (baseStart_6158478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158478 prefixEnd_6158478 := by exact prefixLift 6158478
  have htrace : WordTrace (prefixWord ++ tailWord_6158478) baseStart_6158478 baseEnd_6158478 := by
    simpa [prefixWord, tailWord_6158478, baseEnd_6158478] using wordTrace_append hprefix tailTrace_6158478
  have hstable : (prefixWord ++ tailWord_6158478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158478).length < 2 ^ (prefixWord ++ tailWord_6158478).sum := by decide
  have hdescent : baseEnd_6158478 < baseStart_6158478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158481 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_6158481 : Nat := 118140960795 + 6158481 * 2 ^ 59
def prefixEnd_6158481 : Nat := 4983230072969 + 3 ^ 40 * 6158481 * 2
def baseEnd_6158481 : Nat := 3162260854581824648465167

theorem tailTrace_6158481 : CollatzResearch.WordTrace tailWord_6158481 prefixEnd_6158481 3162260854581824648465167 := by
  unfold tailWord_6158481
  simp only [CollatzResearch.WordTrace]
  refine ⟨224618255201882596663043297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149745503467921731108695531 224618255201882596663043297)
  ·
    refine ⟨168463691401411947497282473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224618255201882596663043297 168463691401411947497282473)
    ·
      refine ⟨126347768551058960622961855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168463691401411947497282473 126347768551058960622961855)
      ·
        refine ⟨189521652826588440934442783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126347768551058960622961855 189521652826588440934442783)
        ·
          refine ⟨284282479239882661401664175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189521652826588440934442783 284282479239882661401664175)
          ·
            refine ⟨426423718859823992102496263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284282479239882661401664175 426423718859823992102496263)
            ·
              refine ⟨639635578289735988153744395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426423718859823992102496263 639635578289735988153744395)
              ·
                refine ⟨959453367434603982230616593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639635578289735988153744395 959453367434603982230616593)
                ·
                  refine ⟨719590025575952986672962445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 959453367434603982230616593 719590025575952986672962445)
                  ·
                    refine ⟨269846259590982370002360917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 719590025575952986672962445 269846259590982370002360917)
                    ·
                      refine ⟨3162260854581824648465167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 269846259590982370002360917 3162260854581824648465167)
                      ·
                        rfl

theorem cell23_6158481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_6158481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158481 prefixEnd_6158481 := by exact prefixLift 6158481
  have htrace : WordTrace (prefixWord ++ tailWord_6158481) baseStart_6158481 baseEnd_6158481 := by
    simpa [prefixWord, tailWord_6158481, baseEnd_6158481] using wordTrace_append hprefix tailTrace_6158481
  have hstable : (prefixWord ++ tailWord_6158481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158481).length < 2 ^ (prefixWord ++ tailWord_6158481).sum := by decide
  have hdescent : baseEnd_6158481 < baseStart_6158481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158482 : List Nat := [3, 2, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_6158482 : Nat := 118140960795 + 6158482 * 2 ^ 59
def prefixEnd_6158482 : Nat := 4983230072969 + 3 ^ 40 * 6158482 * 2
def baseEnd_6158482 : Nat := 1054087122687493048184221

theorem tailTrace_6158482 : CollatzResearch.WordTrace tailWord_6158482 prefixEnd_6158482 1054087122687493048184221 := by
  unfold tailWord_6158482
  simp only [CollatzResearch.WordTrace]
  refine ⟨56154572918719743458457425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149745527783252649222553133 56154572918719743458457425)
  ·
    refine ⟨42115929689039807593843069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56154572918719743458457425 42115929689039807593843069)
    ·
      refine ⟨15793473633389927847691151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42115929689039807593843069 15793473633389927847691151)
      ·
        refine ⟨23690210450084891771536727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15793473633389927847691151 23690210450084891771536727)
        ·
          refine ⟨35535315675127337657305091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23690210450084891771536727 35535315675127337657305091)
          ·
            refine ⟨53302973512691006485957637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35535315675127337657305091 53302973512691006485957637)
            ·
              refine ⟨9994307533629563716117057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53302973512691006485957637 9994307533629563716117057)
              ·
                refine ⟨7495730650222172787087793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9994307533629563716117057 7495730650222172787087793)
                ·
                  refine ⟨5621797987666629590315845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7495730650222172787087793 5621797987666629590315845)
                  ·
                    refine ⟨1054087122687493048184221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5621797987666629590315845 1054087122687493048184221)
                    ·
                      rfl

theorem cell23_6158482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_6158482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158482 prefixEnd_6158482 := by exact prefixLift 6158482
  have htrace : WordTrace (prefixWord ++ tailWord_6158482) baseStart_6158482 baseEnd_6158482 := by
    simpa [prefixWord, tailWord_6158482, baseEnd_6158482] using wordTrace_append hprefix tailTrace_6158482
  have hstable : (prefixWord ++ tailWord_6158482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158482).length < 2 ^ (prefixWord ++ tailWord_6158482).sum := by decide
  have hdescent : baseEnd_6158482 < baseStart_6158482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158491 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 1, 9]
def baseStart_6158491 : Nat := 118140960795 + 6158491 * 2 ^ 59
def prefixEnd_6158491 : Nat := 4983230072969 + 3 ^ 40 * 6158491 * 2
def baseEnd_6158491 : Nat := 1054088663129456536446707

theorem tailTrace_6158491 : CollatzResearch.WordTrace tailWord_6158491 prefixEnd_6158491 1054088663129456536446707 := by
  unfold tailWord_6158491
  simp only [CollatzResearch.WordTrace]
  refine ⟨224618619931846368370907327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149745746621230912247271551 224618619931846368370907327)
  ·
    refine ⟨336927929897769552556360991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224618619931846368370907327 336927929897769552556360991)
    ·
      refine ⟨505391894846654328834541487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336927929897769552556360991 505391894846654328834541487)
      ·
        refine ⟨758087842269981493251812231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505391894846654328834541487 758087842269981493251812231)
        ·
          refine ⟨1137131763404972239877718347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758087842269981493251812231 1137131763404972239877718347)
          ·
            refine ⟨1705697645107458359816577521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137131763404972239877718347 1705697645107458359816577521)
            ·
              refine ⟨1279273233830593769862433141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705697645107458359816577521 1279273233830593769862433141)
              ·
                refine ⟨119931865671618165924603107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1279273233830593769862433141 119931865671618165924603107)
                ·
                  refine ⟨179897798507427248886904661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119931865671618165924603107 179897798507427248886904661)
                  ·
                    refine ⟨1054088663129456536446707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 179897798507427248886904661 1054088663129456536446707)
                    ·
                      rfl

theorem cell23_6158491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 9].length) (baseStart_6158491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158491 prefixEnd_6158491 := by exact prefixLift 6158491
  have htrace : WordTrace (prefixWord ++ tailWord_6158491) baseStart_6158491 baseEnd_6158491 := by
    simpa [prefixWord, tailWord_6158491, baseEnd_6158491] using wordTrace_append hprefix tailTrace_6158491
  have hstable : (prefixWord ++ tailWord_6158491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158491).length < 2 ^ (prefixWord ++ tailWord_6158491).sum := by decide
  have hdescent : baseEnd_6158491 < baseStart_6158491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158495 : List Nat := [1, 1, 2, 6, 1, 3, 1, 8]
def baseStart_6158495 : Nat := 118140960795 + 6158495 * 2 ^ 59
def prefixEnd_6158495 : Nat := 4983230072969 + 3 ^ 40 * 6158495 * 2
def baseEnd_6158495 : Nat := 117121038641147688655189

theorem tailTrace_6158495 : CollatzResearch.WordTrace tailWord_6158495 prefixEnd_6158495 117121038641147688655189 := by
  unfold tailWord_6158495
  simp only [CollatzResearch.WordTrace]
  refine ⟨224618765823831877054052939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149745843882554584702701959 224618765823831877054052939)
  ·
    refine ⟨336928148735747815581079409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224618765823831877054052939 336928148735747815581079409)
    ·
      refine ⟨252696111551810861685809557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336928148735747815581079409 252696111551810861685809557)
      ·
        refine ⟨11845130228991134141522323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 252696111551810861685809557 11845130228991134141522323)
        ·
          refine ⟨17767695343486701212283485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11845130228991134141522323 17767695343486701212283485)
          ·
            refine ⟨6662885753807512954606307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17767695343486701212283485 6662885753807512954606307)
            ·
              refine ⟨9994328630711269431909461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6662885753807512954606307 9994328630711269431909461)
              ·
                refine ⟨117121038641147688655189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9994328630711269431909461 117121038641147688655189)
                ·
                  rfl

theorem cell23_6158495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 8].length) (baseStart_6158495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158495 prefixEnd_6158495 := by exact prefixLift 6158495
  have htrace : WordTrace (prefixWord ++ tailWord_6158495) baseStart_6158495 baseEnd_6158495 := by
    simpa [prefixWord, tailWord_6158495, baseEnd_6158495] using wordTrace_append hprefix tailTrace_6158495
  have hstable : (prefixWord ++ tailWord_6158495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158495).length < 2 ^ (prefixWord ++ tailWord_6158495).sum := by decide
  have hdescent : baseEnd_6158495 < baseStart_6158495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158506 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_6158506 : Nat := 118140960795 + 6158506 * 2 ^ 59
def prefixEnd_6158506 : Nat := 4983230072969 + 3 ^ 40 * 6158506 * 2
def baseEnd_6158506 : Nat := 3162273691598187050652553

theorem tailTrace_6158506 : CollatzResearch.WordTrace tailWord_6158506 prefixEnd_6158506 3162273691598187050652553 := by
  unfold tailWord_6158506
  simp only [CollatzResearch.WordTrace]
  refine ⟨56154791756698006483175843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149746111351194683955135581 56154791756698006483175843)
  ·
    refine ⟨84232187635047009724763765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56154791756698006483175843 84232187635047009724763765)
    ·
      refine ⟨7896767590785657161696603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84232187635047009724763765 7896767590785657161696603)
      ·
        refine ⟨11845151386178485742544905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7896767590785657161696603 11845151386178485742544905)
        ·
          refine ⟨8883863539633864306908679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11845151386178485742544905 8883863539633864306908679)
          ·
            refine ⟨13325795309450796460363019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8883863539633864306908679 13325795309450796460363019)
            ·
              refine ⟨19988692964176194690544529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13325795309450796460363019 19988692964176194690544529)
              ·
                refine ⟨14991519723132146017908397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19988692964176194690544529 14991519723132146017908397)
                ·
                  refine ⟨5621819896174554756715649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14991519723132146017908397 5621819896174554756715649)
                  ·
                    refine ⟨4216364922130916067536737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5621819896174554756715649 4216364922130916067536737)
                    ·
                      refine ⟨3162273691598187050652553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216364922130916067536737 3162273691598187050652553)
                      ·
                        rfl

theorem cell23_6158506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_6158506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158506 prefixEnd_6158506 := by exact prefixLift 6158506
  have htrace : WordTrace (prefixWord ++ tailWord_6158506) baseStart_6158506 baseEnd_6158506 := by
    simpa [prefixWord, tailWord_6158506, baseEnd_6158506] using wordTrace_append hprefix tailTrace_6158506
  have hstable : (prefixWord ++ tailWord_6158506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158506).length < 2 ^ (prefixWord ++ tailWord_6158506).sum := by decide
  have hdescent : baseEnd_6158506 < baseStart_6158506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158526 : List Nat := [4, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_6158526 : Nat := 118140960795 + 6158526 * 2 ^ 59
def prefixEnd_6158526 : Nat := 4983230072969 + 3 ^ 40 * 6158526 * 2
def baseEnd_6158526 : Nat := 3162283961211276972402461

theorem tailTrace_6158526 : CollatzResearch.WordTrace tailWord_6158526 prefixEnd_6158526 3162283961211276972402461 := by
  unfold tailWord_6158526
  simp only [CollatzResearch.WordTrace]
  refine ⟨28077487060839946168553929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149746597657813046232287621 28077487060839946168553929)
  ·
    refine ⟨21058115295629959626415447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28077487060839946168553929 21058115295629959626415447)
    ·
      refine ⟨31587172943444939439623171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21058115295629959626415447 31587172943444939439623171)
      ·
        refine ⟨47380759415167409159434757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31587172943444939439623171 47380759415167409159434757)
        ·
          refine ⟨8883892390343889217394017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47380759415167409159434757 8883892390343889217394017)
          ·
            refine ⟨6662919292757916913045513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8883892390343889217394017 6662919292757916913045513)
            ·
              refine ⟨4997189469568437684784135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6662919292757916913045513 4997189469568437684784135)
              ·
                refine ⟨7495784204352656527176203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997189469568437684784135 7495784204352656527176203)
                ·
                  refine ⟨11243676306528984790764305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7495784204352656527176203 11243676306528984790764305)
                  ·
                    refine ⟨8432757229896738593073229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11243676306528984790764305 8432757229896738593073229)
                    ·
                      refine ⟨3162283961211276972402461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8432757229896738593073229 3162283961211276972402461)
                      ·
                        rfl

theorem cell23_6158526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_6158526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158526 prefixEnd_6158526 := by exact prefixLift 6158526
  have htrace : WordTrace (prefixWord ++ tailWord_6158526) baseStart_6158526 baseEnd_6158526 := by
    simpa [prefixWord, tailWord_6158526, baseEnd_6158526] using wordTrace_append hprefix tailTrace_6158526
  have hstable : (prefixWord ++ tailWord_6158526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158526).length < 2 ^ (prefixWord ++ tailWord_6158526).sum := by decide
  have hdescent : baseEnd_6158526 < baseStart_6158526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158538 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 4, 6]
def baseStart_6158538 : Nat := 118140960795 + 6158538 * 2 ^ 59
def prefixEnd_6158538 : Nat := 4983230072969 + 3 ^ 40 * 6158538 * 2
def baseEnd_6158538 : Nat := 1054096707659710308484135

theorem tailTrace_6158538 : CollatzResearch.WordTrace tailWord_6158538 prefixEnd_6158538 1054096707659710308484135 := by
  unfold tailWord_6158538
  simp only [CollatzResearch.WordTrace]
  refine ⟨56155083540669023849467067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149746889441784063598578845 56155083540669023849467067)
  ·
    refine ⟨84232625311003535774200601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56155083540669023849467067 84232625311003535774200601)
    ·
      refine ⟨63174468983252651830650451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84232625311003535774200601 63174468983252651830650451)
      ·
        refine ⟨94761703474878977745975677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63174468983252651830650451 94761703474878977745975677)
        ·
          refine ⟨35535638803079616654740879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94761703474878977745975677 35535638803079616654740879)
          ·
            refine ⟨53303458204619424982111319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35535638803079616654740879 53303458204619424982111319)
            ·
              refine ⟨79955187306929137473166979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53303458204619424982111319 79955187306929137473166979)
              ·
                refine ⟨119932780960393706209750469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79955187306929137473166979 119932780960393706209750469)
                ·
                  refine ⟨22487396430073819914328213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119932780960393706209750469 22487396430073819914328213)
                  ·
                    refine ⟨1054096707659710308484135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22487396430073819914328213 1054096707659710308484135)
                    ·
                      rfl

theorem cell23_6158538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_6158538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158538 prefixEnd_6158538 := by exact prefixLift 6158538
  have htrace : WordTrace (prefixWord ++ tailWord_6158538) baseStart_6158538 baseEnd_6158538 := by
    simpa [prefixWord, tailWord_6158538, baseEnd_6158538] using wordTrace_append hprefix tailTrace_6158538
  have hstable : (prefixWord ++ tailWord_6158538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158538).length < 2 ^ (prefixWord ++ tailWord_6158538).sum := by decide
  have hdescent : baseEnd_6158538 < baseStart_6158538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158545 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 3, 4, 2]
def baseStart_6158545 : Nat := 118140960795 + 6158545 * 2 ^ 59
def prefixEnd_6158545 : Nat := 4983230072969 + 3 ^ 40 * 6158545 * 2
def baseEnd_6158545 : Nat := 3162293717343712398064873

theorem tailTrace_6158545 : CollatzResearch.WordTrace tailWord_6158545 prefixEnd_6158545 3162293717343712398064873 := by
  unfold tailWord_6158545
  simp only [CollatzResearch.WordTrace]
  refine ⟨224620589473650735593373089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149747059649100490395582059 224620589473650735593373089)
  ·
    refine ⟨168465442105238051695029817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224620589473650735593373089 168465442105238051695029817)
    ·
      refine ⟨126349081578928538771272363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168465442105238051695029817 126349081578928538771272363)
      ·
        refine ⟨189523622368392808156908545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126349081578928538771272363 189523622368392808156908545)
        ·
          refine ⟨142142716776294606117681409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189523622368392808156908545 142142716776294606117681409)
          ·
            refine ⟨106607037582220954588261057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142142716776294606117681409 106607037582220954588261057)
            ·
              refine ⟨79955278186665715941195793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106607037582220954588261057 79955278186665715941195793)
              ·
                refine ⟨59966458639999286955896845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79955278186665715941195793 59966458639999286955896845)
                ·
                  refine ⟨22487421989999732608461317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59966458639999286955896845 22487421989999732608461317)
                  ·
                    refine ⟨4216391623124949864086497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22487421989999732608461317 4216391623124949864086497)
                    ·
                      refine ⟨3162293717343712398064873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216391623124949864086497 3162293717343712398064873)
                      ·
                        rfl

theorem cell23_6158545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 4, 2].length) (baseStart_6158545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158545 prefixEnd_6158545 := by exact prefixLift 6158545
  have htrace : WordTrace (prefixWord ++ tailWord_6158545) baseStart_6158545 baseEnd_6158545 := by
    simpa [prefixWord, tailWord_6158545, baseEnd_6158545] using wordTrace_append hprefix tailTrace_6158545
  have hstable : (prefixWord ++ tailWord_6158545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158545).length < 2 ^ (prefixWord ++ tailWord_6158545).sum := by decide
  have hdescent : baseEnd_6158545 < baseStart_6158545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158556 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_6158556 : Nat := 118140960795 + 6158556 * 2 ^ 59
def prefixEnd_6158556 : Nat := 4983230072969 + 3 ^ 40 * 6158556 * 2
def baseEnd_6158556 : Nat := 3162299365630911855027323

theorem tailTrace_6158556 : CollatzResearch.WordTrace tailWord_6158556 prefixEnd_6158556 3162299365630911855027323 := by
  unfold tailWord_6158556
  simp only [CollatzResearch.WordTrace]
  refine ⟨112310495338305442236011761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149747327117740589648015681 112310495338305442236011761)
  ·
    refine ⟨84232871503729081677008821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112310495338305442236011761 84232871503729081677008821)
    ·
      refine ⟨7896831703474601407219577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84232871503729081677008821 7896831703474601407219577)
      ·
        refine ⟨5922623777605951055414683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7896831703474601407219577 5922623777605951055414683)
        ·
          refine ⟨8883935666408926583122025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5922623777605951055414683 8883935666408926583122025)
          ·
            refine ⟨6662951749806694937341519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8883935666408926583122025 6662951749806694937341519)
            ·
              refine ⟨9994427624710042406012279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6662951749806694937341519 9994427624710042406012279)
              ·
                refine ⟨14991641437065063609018419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9994427624710042406012279 14991641437065063609018419)
                ·
                  refine ⟨22487462155597595413527629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14991641437065063609018419 22487462155597595413527629)
                  ·
                    refine ⟨8432798308349098280072861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22487462155597595413527629 8432798308349098280072861)
                    ·
                      refine ⟨3162299365630911855027323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8432798308349098280072861 3162299365630911855027323)
                      ·
                        rfl

theorem cell23_6158556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_6158556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158556 prefixEnd_6158556 := by exact prefixLift 6158556
  have htrace : WordTrace (prefixWord ++ tailWord_6158556) baseStart_6158556 baseEnd_6158556 := by
    simpa [prefixWord, tailWord_6158556, baseEnd_6158556] using wordTrace_append hprefix tailTrace_6158556
  have hstable : (prefixWord ++ tailWord_6158556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158556).length < 2 ^ (prefixWord ++ tailWord_6158556).sum := by decide
  have hdescent : baseEnd_6158556 < baseStart_6158556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158585 : List Nat := [1, 2, 1, 3, 1, 1, 2, 7, 5]
def baseStart_6158585 : Nat := 118140960795 + 6158585 * 2 ^ 59
def prefixEnd_6158585 : Nat := 4983230072969 + 3 ^ 40 * 6158585 * 2
def baseEnd_6158585 : Nat := 351368250729988026840521

theorem tailTrace_6158585 : CollatzResearch.WordTrace tailWord_6158585 prefixEnd_6158585 351368250729988026840521 := by
  unfold tailWord_6158585
  simp only [CollatzResearch.WordTrace]
  refine ⟨224622048393505822424829209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149748032262337214949886139 224622048393505822424829209)
  ·
    refine ⟨168466536295129366818621907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224622048393505822424829209 168466536295129366818621907)
    ·
      refine ⟨252699804442694050227932861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168466536295129366818621907 252699804442694050227932861)
      ·
        refine ⟨94762426666010268835474823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252699804442694050227932861 94762426666010268835474823)
        ·
          refine ⟨142143639999015403253212235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94762426666010268835474823 142143639999015403253212235)
          ·
            refine ⟨213215459998523104879818353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142143639999015403253212235 213215459998523104879818353)
            ·
              refine ⟨159911594998892328659863765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213215459998523104879818353 159911594998892328659863765)
              ·
                refine ⟨3747928007786538952965557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 159911594998892328659863765 3747928007786538952965557)
                ·
                  refine ⟨351368250729988026840521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3747928007786538952965557 351368250729988026840521)
                  ·
                    rfl

theorem cell23_6158585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 5].length) (baseStart_6158585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158585 prefixEnd_6158585 := by exact prefixLift 6158585
  have htrace : WordTrace (prefixWord ++ tailWord_6158585) baseStart_6158585 baseEnd_6158585 := by
    simpa [prefixWord, tailWord_6158585, baseEnd_6158585] using wordTrace_append hprefix tailTrace_6158585
  have hstable : (prefixWord ++ tailWord_6158585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158585).length < 2 ^ (prefixWord ++ tailWord_6158585).sum := by decide
  have hdescent : baseEnd_6158585 < baseStart_6158585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158652 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 2, 4, 2]
def baseStart_6158652 : Nat := 118140960795 + 6158652 * 2 ^ 59
def prefixEnd_6158652 : Nat := 4983230072969 + 3 ^ 40 * 6158652 * 2
def baseEnd_6158652 : Nat := 3162348659773743479426881

theorem tailTrace_6158652 : CollatzResearch.WordTrace tailWord_6158652 prefixEnd_6158652 3162348659773743479426881 := by
  unfold tailWord_6158652
  simp only [CollatzResearch.WordTrace]
  refine ⟨112312246042131546433759105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149749661389508728578345473 112312246042131546433759105)
  ·
    refine ⟨84234184531598659825319329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112312246042131546433759105 84234184531598659825319329)
    ·
      refine ⟨63175638398698994868989497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84234184531598659825319329 63175638398698994868989497)
      ·
        refine ⟨47381728799024246151742123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63175638398698994868989497 47381728799024246151742123)
        ·
          refine ⟨71072593198536369227613185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47381728799024246151742123 71072593198536369227613185)
          ·
            refine ⟨53304444898902276920709889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71072593198536369227613185 53304444898902276920709889)
            ·
              refine ⟨39978333674176707690532417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53304444898902276920709889 39978333674176707690532417)
              ·
                refine ⟨29983750255632530767899313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39978333674176707690532417 29983750255632530767899313)
                ·
                  refine ⟨22487812691724398075924485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29983750255632530767899313 22487812691724398075924485)
                  ·
                    refine ⟨4216464879698324639235841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22487812691724398075924485 4216464879698324639235841)
                    ·
                      refine ⟨3162348659773743479426881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216464879698324639235841 3162348659773743479426881)
                      ·
                        rfl

theorem cell23_6158652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_6158652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158652 prefixEnd_6158652 := by exact prefixLift 6158652
  have htrace : WordTrace (prefixWord ++ tailWord_6158652) baseStart_6158652 baseEnd_6158652 := by
    simpa [prefixWord, tailWord_6158652, baseEnd_6158652] using wordTrace_append hprefix tailTrace_6158652
  have hstable : (prefixWord ++ tailWord_6158652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158652).length < 2 ^ (prefixWord ++ tailWord_6158652).sum := by decide
  have hdescent : baseEnd_6158652 < baseStart_6158652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158696 : List Nat := [2, 1, 4, 2, 2, 2, 2, 3, 1, 4]
def baseStart_6158696 : Nat := 118140960795 + 6158696 * 2 ^ 59
def prefixEnd_6158696 : Nat := 4983230072969 + 3 ^ 40 * 6158696 * 2
def baseEnd_6158696 : Nat := 1054123750974180435758893

theorem tailTrace_6158696 : CollatzResearch.WordTrace tailWord_6158696 prefixEnd_6158696 1054123750974180435758893 := by
  unfold tailWord_6158696
  simp only [CollatzResearch.WordTrace]
  refine ⟨112313048448051844191059971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149750731264069125588079961 112313048448051844191059971)
  ·
    refine ⟨168469572672077766286589957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112313048448051844191059971 168469572672077766286589957)
    ·
      refine ⟨31588044876014581178735617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168469572672077766286589957 31588044876014581178735617)
      ·
        refine ⟨23691033657010935884051713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31588044876014581178735617 23691033657010935884051713)
        ·
          refine ⟨17768275242758201913038785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23691033657010935884051713 17768275242758201913038785)
          ·
            refine ⟨13326206432068651434779089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17768275242758201913038785 13326206432068651434779089)
            ·
              refine ⟨9994654824051488576084317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13326206432068651434779089 9994654824051488576084317)
              ·
                refine ⟨3747995559019308216031619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9994654824051488576084317 3747995559019308216031619)
                ·
                  refine ⟨5621993338528962324047429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3747995559019308216031619 5621993338528962324047429)
                  ·
                    refine ⟨1054123750974180435758893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5621993338528962324047429 1054123750974180435758893)
                    ·
                      rfl

theorem cell23_6158696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_6158696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158696 prefixEnd_6158696 := by exact prefixLift 6158696
  have htrace : WordTrace (prefixWord ++ tailWord_6158696) baseStart_6158696 baseEnd_6158696 := by
    simpa [prefixWord, tailWord_6158696, baseEnd_6158696] using wordTrace_append hprefix tailTrace_6158696
  have hstable : (prefixWord ++ tailWord_6158696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158696).length < 2 ^ (prefixWord ++ tailWord_6158696).sum := by decide
  have hdescent : baseEnd_6158696 < baseStart_6158696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158709 : List Nat := [1, 3, 4, 1, 2, 3, 1, 2, 6]
def baseStart_6158709 : Nat := 118140960795 + 6158709 * 2 ^ 59
def prefixEnd_6158709 : Nat := 4983230072969 + 3 ^ 40 * 6158709 * 2
def baseEnd_6158709 : Nat := 351375325352338861823791

theorem tailTrace_6158709 : CollatzResearch.WordTrace tailWord_6158709 prefixEnd_6158709 351375325352338861823791 := by
  unfold tailWord_6158709
  simp only [CollatzResearch.WordTrace]
  refine ⟨224626571045056591602343181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149751047363371061068228787 224626571045056591602343181)
  ·
    refine ⟨84234964141896221850878693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224626571045056591602343181 84234964141896221850878693)
    ·
      refine ⟨15794055776605541597039755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84234964141896221850878693 15794055776605541597039755)
      ·
        refine ⟨23691083664908312395559633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15794055776605541597039755 23691083664908312395559633)
        ·
          refine ⟨17768312748681234296669725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23691083664908312395559633 17768312748681234296669725)
          ·
            refine ⟨6663117280755462861251147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17768312748681234296669725 6663117280755462861251147)
            ·
              refine ⟨9994675921133194291876721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6663117280755462861251147 9994675921133194291876721)
              ·
                refine ⟨7496006940849895718907541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9994675921133194291876721 7496006940849895718907541)
                ·
                  refine ⟨351375325352338861823791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7496006940849895718907541 351375325352338861823791)
                  ·
                    rfl

theorem cell23_6158709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_6158709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158709 prefixEnd_6158709 := by exact prefixLift 6158709
  have htrace : WordTrace (prefixWord ++ tailWord_6158709) baseStart_6158709 baseEnd_6158709 := by
    simpa [prefixWord, tailWord_6158709, baseEnd_6158709] using wordTrace_append hprefix tailTrace_6158709
  have hstable : (prefixWord ++ tailWord_6158709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158709).length < 2 ^ (prefixWord ++ tailWord_6158709).sum := by decide
  have hdescent : baseEnd_6158709 < baseStart_6158709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158745 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 5]
def baseStart_6158745 : Nat := 118140960795 + 6158745 * 2 ^ 59
def prefixEnd_6158745 : Nat := 4983230072969 + 3 ^ 40 * 6158745 * 2
def baseEnd_6158745 : Nat := 3162396413474611615563953

theorem tailTrace_6158745 : CollatzResearch.WordTrace tailWord_6158745 prefixEnd_6158745 3162396413474611615563953 := by
  unfold tailWord_6158745
  simp only [CollatzResearch.WordTrace]
  refine ⟨224627884072926169750653689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149751922715284113167102459 224627884072926169750653689)
  ·
    refine ⟨168470913054694627312990267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224627884072926169750653689 168470913054694627312990267)
    ·
      refine ⟨252706369582041940969485401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168470913054694627312990267 252706369582041940969485401)
      ·
        refine ⟨189529777186531455727114051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252706369582041940969485401 189529777186531455727114051)
        ·
          refine ⟨284294665779797183590671077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189529777186531455727114051 284294665779797183590671077)
          ·
            refine ⟨53305249833711971923250827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284294665779797183590671077 53305249833711971923250827)
            ·
              refine ⟨79957874750567957884876241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53305249833711971923250827 79957874750567957884876241)
              ·
                refine ⟨59968406062925968413657181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79957874750567957884876241 59968406062925968413657181)
                ·
                  refine ⟨22488152273597238155121443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59968406062925968413657181 22488152273597238155121443)
                  ·
                    refine ⟨33732228410395857232682165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22488152273597238155121443 33732228410395857232682165)
                    ·
                      refine ⟨3162396413474611615563953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33732228410395857232682165 3162396413474611615563953)
                      ·
                        rfl

theorem cell23_6158745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_6158745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158745 prefixEnd_6158745 := by exact prefixLift 6158745
  have htrace : WordTrace (prefixWord ++ tailWord_6158745) baseStart_6158745 baseEnd_6158745 := by
    simpa [prefixWord, tailWord_6158745, baseEnd_6158745] using wordTrace_append hprefix tailTrace_6158745
  have hstable : (prefixWord ++ tailWord_6158745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158745).length < 2 ^ (prefixWord ++ tailWord_6158745).sum := by decide
  have hdescent : baseEnd_6158745 < baseStart_6158745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158752 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 4, 4]
def baseStart_6158752 : Nat := 118140960795 + 6158752 * 2 ^ 59
def prefixEnd_6158752 : Nat := 4983230072969 + 3 ^ 40 * 6158752 * 2
def baseEnd_6158752 : Nat := 1054133335946397696058807

theorem tailTrace_6158752 : CollatzResearch.WordTrace tailWord_6158752 prefixEnd_6158752 1054133335946397696058807 := by
  unfold tailWord_6158752
  simp only [CollatzResearch.WordTrace]
  refine ⟨112314069691950404973079255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149752092922600539964105673 112314069691950404973079255)
  ·
    refine ⟨168471104537925607459618883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112314069691950404973079255 168471104537925607459618883)
    ·
      refine ⟨252706656806888411189428325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168471104537925607459618883 252706656806888411189428325)
      ·
        refine ⟨47382498151291577098017811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252706656806888411189428325 47382498151291577098017811)
        ·
          refine ⟨71073747226937365647026717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47382498151291577098017811 71073747226937365647026717)
          ·
            refine ⟨26652655210101512117635019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71073747226937365647026717 26652655210101512117635019)
            ·
              refine ⟨39978982815152268176452529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26652655210101512117635019 39978982815152268176452529)
              ·
                refine ⟨29984237111364201132339397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39978982815152268176452529 29984237111364201132339397)
                ·
                  refine ⟨5622044458380787712313637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29984237111364201132339397 5622044458380787712313637)
                  ·
                    refine ⟨1054133335946397696058807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5622044458380787712313637 1054133335946397696058807)
                    ·
                      rfl

theorem cell23_6158752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 4, 4].length) (baseStart_6158752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158752 prefixEnd_6158752 := by exact prefixLift 6158752
  have htrace : WordTrace (prefixWord ++ tailWord_6158752) baseStart_6158752 baseEnd_6158752 := by
    simpa [prefixWord, tailWord_6158752, baseEnd_6158752] using wordTrace_append hprefix tailTrace_6158752
  have hstable : (prefixWord ++ tailWord_6158752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158752).length < 2 ^ (prefixWord ++ tailWord_6158752).sum := by decide
  have hdescent : baseEnd_6158752 < baseStart_6158752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158759 : List Nat := [1, 1, 6, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_6158759 : Nat := 118140960795 + 6158759 * 2 ^ 59
def prefixEnd_6158759 : Nat := 4983230072969 + 3 ^ 40 * 6158759 * 2
def baseEnd_6158759 : Nat := 3162403602203774560788889

theorem tailTrace_6158759 : CollatzResearch.WordTrace tailWord_6158759 prefixEnd_6158759 3162403602203774560788889 := by
  unfold tailWord_6158759
  simp only [CollatzResearch.WordTrace]
  refine ⟨224628394694875450141663331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149752263129916966761108887 224628394694875450141663331)
  ·
    refine ⟨336942592042313175212494997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224628394694875450141663331 336942592042313175212494997)
    ·
      refine ⟨15794184001983430088085703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 336942592042313175212494997 15794184001983430088085703)
      ·
        refine ⟨23691276002975145132128555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15794184001983430088085703 23691276002975145132128555)
        ·
          refine ⟨35536914004462717698192833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23691276002975145132128555 35536914004462717698192833)
          ·
            refine ⟨26652685503347038273644625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35536914004462717698192833 26652685503347038273644625)
            ·
              refine ⟨19989514127510278705233469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26652685503347038273644625 19989514127510278705233469)
              ·
                refine ⟨7496067797816354514462551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19989514127510278705233469 7496067797816354514462551)
                ·
                  refine ⟨11244101696724531771693827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7496067797816354514462551 11244101696724531771693827)
                  ·
                    refine ⟨16866152545086797657540741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11244101696724531771693827 16866152545086797657540741)
                    ·
                      refine ⟨3162403602203774560788889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16866152545086797657540741 3162403602203774560788889)
                      ·
                        rfl

theorem cell23_6158759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_6158759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158759 prefixEnd_6158759 := by exact prefixLift 6158759
  have htrace : WordTrace (prefixWord ++ tailWord_6158759) baseStart_6158759 baseEnd_6158759 := by
    simpa [prefixWord, tailWord_6158759, baseEnd_6158759] using wordTrace_append hprefix tailTrace_6158759
  have hstable : (prefixWord ++ tailWord_6158759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158759).length < 2 ^ (prefixWord ++ tailWord_6158759).sum := by decide
  have hdescent : baseEnd_6158759 < baseStart_6158759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158826 : List Nat := [3, 1, 3, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_6158826 : Nat := 118140960795 + 6158826 * 2 ^ 59
def prefixEnd_6158826 : Nat := 4983230072969 + 3 ^ 40 * 6158826 * 2
def baseEnd_6158826 : Nat := 3162438005407625798651081

theorem tailTrace_6158826 : CollatzResearch.WordTrace tailWord_6158826 prefixEnd_6158826 3162438005407625798651081 := by
  unfold tailWord_6158826
  simp only [CollatzResearch.WordTrace]
  refine ⟨56157709596408180146088083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149753892257088480389568221 56157709596408180146088083)
  ·
    refine ⟨84236564394612270219132125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56157709596408180146088083 84236564394612270219132125)
    ·
      refine ⟨31588711647979601332174547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84236564394612270219132125 31588711647979601332174547)
      ·
        refine ⟨47383067471969401998261821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31588711647979601332174547 47383067471969401998261821)
        ·
          refine ⟨17768650301988525749348183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47383067471969401998261821 17768650301988525749348183)
          ·
            refine ⟨26652975452982788624022275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17768650301988525749348183 26652975452982788624022275)
            ·
              refine ⟨39979463179474182936033413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26652975452982788624022275 39979463179474182936033413)
              ·
                refine ⟨7496149346151409300506265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39979463179474182936033413 7496149346151409300506265)
                ·
                  refine ⟨5622112009613556975379699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7496149346151409300506265 5622112009613556975379699)
                  ·
                    refine ⟨8433168014420335463069549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5622112009613556975379699 8433168014420335463069549)
                    ·
                      refine ⟨3162438005407625798651081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8433168014420335463069549 3162438005407625798651081)
                      ·
                        rfl

theorem cell23_6158826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_6158826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158826 prefixEnd_6158826 := by exact prefixLift 6158826
  have htrace : WordTrace (prefixWord ++ tailWord_6158826) baseStart_6158826 baseEnd_6158826 := by
    simpa [prefixWord, tailWord_6158826, baseEnd_6158826] using wordTrace_append hprefix tailTrace_6158826
  have hstable : (prefixWord ++ tailWord_6158826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158826).length < 2 ^ (prefixWord ++ tailWord_6158826).sum := by decide
  have hdescent : baseEnd_6158826 < baseStart_6158826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158883 : List Nat := [1, 1, 1, 4, 4, 1, 3, 2, 2, 2, 2]
def baseStart_6158883 : Nat := 118140960795 + 6158883 * 2 ^ 59
def prefixEnd_6158883 : Nat := 4983230072969 + 3 ^ 40 * 6158883 * 2
def baseEnd_6158883 : Nat := 3162467273804932075638319

theorem tailTrace_6158883 : CollatzResearch.WordTrace tailWord_6158883 prefixEnd_6158883 3162467273804932075638319 := by
  unfold tailWord_6158883
  simp only [CollatzResearch.WordTrace]
  refine ⟨224632917346426219319177303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149755278230950812879451535 224632917346426219319177303)
  ·
    refine ⟨336949376019639328978765955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224632917346426219319177303 336949376019639328978765955)
    ·
      refine ⟨505424064029458993468148933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336949376019639328978765955 505424064029458993468148933)
      ·
        refine ⟨94767012005523561275277925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 505424064029458993468148933 94767012005523561275277925)
        ·
          refine ⟨17768814751035667739114611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94767012005523561275277925 17768814751035667739114611)
          ·
            refine ⟨26653222126553501608671917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17768814751035667739114611 26653222126553501608671917)
            ·
              refine ⟨9994958297457563103251969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26653222126553501608671917 9994958297457563103251969)
              ·
                refine ⟨7496218723093172327438977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9994958297457563103251969 7496218723093172327438977)
                ·
                  refine ⟨5622164042319879245579233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7496218723093172327438977 5622164042319879245579233)
                  ·
                    refine ⟨4216623031739909434184425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5622164042319879245579233 4216623031739909434184425)
                    ·
                      refine ⟨3162467273804932075638319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216623031739909434184425 3162467273804932075638319)
                      ·
                        rfl

theorem cell23_6158883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_6158883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158883 prefixEnd_6158883 := by exact prefixLift 6158883
  have htrace : WordTrace (prefixWord ++ tailWord_6158883) baseStart_6158883 baseEnd_6158883 := by
    simpa [prefixWord, tailWord_6158883, baseEnd_6158883] using wordTrace_append hprefix tailTrace_6158883
  have hstable : (prefixWord ++ tailWord_6158883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158883).length < 2 ^ (prefixWord ++ tailWord_6158883).sum := by decide
  have hdescent : baseEnd_6158883 < baseStart_6158883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158976 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 3]
def baseStart_6158976 : Nat := 118140960795 + 6158976 * 2 ^ 59
def prefixEnd_6158976 : Nat := 4983230072969 + 3 ^ 40 * 6158976 * 2
def baseEnd_6158976 : Nat := 3162515027505800211775391

theorem tailTrace_6158976 : CollatzResearch.WordTrace tailWord_6158976 prefixEnd_6158976 3162515027505800211775391 := by
  unfold tailWord_6158976
  simp only [CollatzResearch.WordTrace]
  refine ⟨112318154667544648101156391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149757539556726197468208521 112318154667544648101156391)
  ·
    refine ⟨168477232001316972151734587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112318154667544648101156391 168477232001316972151734587)
    ·
      refine ⟨252715848001975458227601881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168477232001316972151734587 252715848001975458227601881)
      ·
        refine ⟨189536886001481593670701411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252715848001975458227601881 189536886001481593670701411)
        ·
          refine ⟨284305329002222390506052117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189536886001481593670701411 284305329002222390506052117)
          ·
            refine ⟨13326812296979174554971193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 284305329002222390506052117 13326812296979174554971193)
            ·
              refine ⟨9995109222734380916228395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13326812296979174554971193 9995109222734380916228395)
              ·
                refine ⟨14992663834101571374342593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9995109222734380916228395 14992663834101571374342593)
                ·
                  refine ⟨11244497875576178530756945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14992663834101571374342593 11244497875576178530756945)
                  ·
                    refine ⟨8433373406682133898067709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11244497875576178530756945 8433373406682133898067709)
                    ·
                      refine ⟨3162515027505800211775391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8433373406682133898067709 3162515027505800211775391)
                      ·
                        rfl

theorem cell23_6158976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_6158976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158976 prefixEnd_6158976 := by exact prefixLift 6158976
  have htrace : WordTrace (prefixWord ++ tailWord_6158976) baseStart_6158976 baseEnd_6158976 := by
    simpa [prefixWord, tailWord_6158976, baseEnd_6158976] using wordTrace_append hprefix tailTrace_6158976
  have hstable : (prefixWord ++ tailWord_6158976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158976).length < 2 ^ (prefixWord ++ tailWord_6158976).sum := by decide
  have hdescent : baseEnd_6158976 < baseStart_6158976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6158996 : List Nat := [2, 4, 2, 2, 1, 1, 1, 4, 6]
def baseStart_6158996 : Nat := 118140960795 + 6158996 * 2 ^ 59
def prefixEnd_6158996 : Nat := 4983230072969 + 3 ^ 40 * 6158996 * 2
def baseEnd_6158996 : Nat := 351391699679876681502811

theorem tailTrace_6158996 : CollatzResearch.WordTrace tailWord_6158996 prefixEnd_6158996 351391699679876681502811 := by
  unfold tailWord_6158996
  simp only [CollatzResearch.WordTrace]
  refine ⟨112318519397508419809020421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149758025863344559745360561 112318519397508419809020421)
  ·
    refine ⟨21059722387032828714191329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112318519397508419809020421 21059722387032828714191329)
    ·
      refine ⟨15794791790274621535643497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21059722387032828714191329 15794791790274621535643497)
      ·
        refine ⟨11846093842705966151732623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15794791790274621535643497 11846093842705966151732623)
        ·
          refine ⟨17769140764058949227598935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11846093842705966151732623 17769140764058949227598935)
          ·
            refine ⟨26653711146088423841398403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17769140764058949227598935 26653711146088423841398403)
            ·
              refine ⟨39980566719132635762097605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26653711146088423841398403 39980566719132635762097605)
              ·
                refine ⟨7496356259837369205393301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39980566719132635762097605 7496356259837369205393301)
                ·
                  refine ⟨351391699679876681502811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7496356259837369205393301 351391699679876681502811)
                  ·
                    rfl

theorem cell23_6158996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_6158996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6158996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6158996 prefixEnd_6158996 := by exact prefixLift 6158996
  have htrace : WordTrace (prefixWord ++ tailWord_6158996) baseStart_6158996 baseEnd_6158996 := by
    simpa [prefixWord, tailWord_6158996, baseEnd_6158996] using wordTrace_append hprefix tailTrace_6158996
  have hstable : (prefixWord ++ tailWord_6158996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6158996).length < 2 ^ (prefixWord ++ tailWord_6158996).sum := by decide
  have hdescent : baseEnd_6158996 < baseStart_6158996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6158996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159039 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 1, 6]
def baseStart_6159039 : Nat := 118140960795 + 6159039 * 2 ^ 59
def prefixEnd_6159039 : Nat := 4983230072969 + 3 ^ 40 * 6159039 * 2
def baseEnd_6159039 : Nat := 1054182458929011155095867

theorem tailTrace_6159039 : CollatzResearch.WordTrace tailWord_6159039 prefixEnd_6159039 1054182458929011155095867 := by
  unfold tailWord_6159039
  simp only [CollatzResearch.WordTrace]
  refine ⟨224638607133861057961856171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149759071422574038641237447 224638607133861057961856171)
  ·
    refine ⟨336957910700791586942784257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224638607133861057961856171 336957910700791586942784257)
    ·
      refine ⟨252718433025593690207088193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336957910700791586942784257 252718433025593690207088193)
      ·
        refine ⟨189538824769195267655316145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252718433025593690207088193 189538824769195267655316145)
        ·
          refine ⟨142154118576896450741487109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189538824769195267655316145 142154118576896450741487109)
          ·
            refine ⟨26653897233168084514028833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142154118576896450741487109 26653897233168084514028833)
            ·
              refine ⟨19990422924876063385521625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26653897233168084514028833 19990422924876063385521625)
              ·
                refine ⟨14992817193657047539141219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19990422924876063385521625 14992817193657047539141219)
                ·
                  refine ⟨22489225790485571308711829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14992817193657047539141219 22489225790485571308711829)
                  ·
                    refine ⟨1054182458929011155095867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22489225790485571308711829 1054182458929011155095867)
                    ·
                      rfl

theorem cell23_6159039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 6].length) (baseStart_6159039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159039 prefixEnd_6159039 := by exact prefixLift 6159039
  have htrace : WordTrace (prefixWord ++ tailWord_6159039) baseStart_6159039 baseEnd_6159039 := by
    simpa [prefixWord, tailWord_6159039, baseEnd_6159039] using wordTrace_append hprefix tailTrace_6159039
  have hstable : (prefixWord ++ tailWord_6159039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159039).length < 2 ^ (prefixWord ++ tailWord_6159039).sum := by decide
  have hdescent : baseEnd_6159039 < baseStart_6159039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159040 : List Nat := [2, 1, 1, 2, 4, 3, 2, 3, 1, 1, 3]
def baseStart_6159040 : Nat := 118140960795 + 6159040 * 2 ^ 59
def prefixEnd_6159040 : Nat := 4983230072969 + 3 ^ 40 * 6159040 * 2
def baseEnd_6159040 : Nat := 3162547890267687961375097

theorem tailTrace_6159040 : CollatzResearch.WordTrace tailWord_6159040 prefixEnd_6159040 3162547890267687961375097 := by
  unfold tailWord_6159040
  simp only [CollatzResearch.WordTrace]
  refine ⟨112319321803428717566321287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149759095737904956755095049 112319321803428717566321287)
  ·
    refine ⟨168478982705143076349481931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112319321803428717566321287 168478982705143076349481931)
    ·
      refine ⟨252718474057714614524222897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168478982705143076349481931 252718474057714614524222897)
      ·
        refine ⟨189538855543285960893167173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252718474057714614524222897 189538855543285960893167173)
        ·
          refine ⟨35538535414366117667468845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189538855543285960893167173 35538535414366117667468845)
          ·
            refine ⟨13326950780387294125300817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35538535414366117667468845 13326950780387294125300817)
            ·
              refine ⟨9995213085290470593975613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13326950780387294125300817 9995213085290470593975613)
              ·
                refine ⟨3748204906983926472740855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9995213085290470593975613 3748204906983926472740855)
                ·
                  refine ⟨5622307360475889709111283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3748204906983926472740855 5622307360475889709111283)
                  ·
                    refine ⟨8433461040713834563666925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5622307360475889709111283 8433461040713834563666925)
                    ·
                      refine ⟨3162547890267687961375097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8433461040713834563666925 3162547890267687961375097)
                      ·
                        rfl

theorem cell23_6159040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 1, 1, 3].length) (baseStart_6159040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159040 prefixEnd_6159040 := by exact prefixLift 6159040
  have htrace : WordTrace (prefixWord ++ tailWord_6159040) baseStart_6159040 baseEnd_6159040 := by
    simpa [prefixWord, tailWord_6159040, baseEnd_6159040] using wordTrace_append hprefix tailTrace_6159040
  have hstable : (prefixWord ++ tailWord_6159040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159040).length < 2 ^ (prefixWord ++ tailWord_6159040).sum := by decide
  have hdescent : baseEnd_6159040 < baseStart_6159040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159063 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 3, 2, 2]
def baseStart_6159063 : Nat := 118140960795 + 6159063 * 2 ^ 59
def prefixEnd_6159063 : Nat := 4983230072969 + 3 ^ 40 * 6159063 * 2
def baseEnd_6159063 : Nat := 3162559700322741371387491

theorem tailTrace_6159063 : CollatzResearch.WordTrace tailWord_6159063 prefixEnd_6159063 3162559700322741371387491 := by
  unfold tailWord_6159063
  simp only [CollatzResearch.WordTrace]
  refine ⟨224639482485774110060729843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149759654990516073373819895 224639482485774110060729843)
  ·
    refine ⟨336959223728661165091094765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224639482485774110060729843 336959223728661165091094765)
    ·
      refine ⟨126359708898247936909160537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336959223728661165091094765 126359708898247936909160537)
      ·
        refine ⟨94769781673685952681870403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126359708898247936909160537 94769781673685952681870403)
        ·
          refine ⟨142154672510528929022805605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94769781673685952681870403 142154672510528929022805605)
          ·
            refine ⟨26654001095724174191776051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142154672510528929022805605 26654001095724174191776051)
            ·
              refine ⟨39981001643586261287664077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26654001095724174191776051 39981001643586261287664077)
              ·
                refine ⟨14992875616344847982874029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39981001643586261287664077 14992875616344847982874029)
                ·
                  refine ⟨5622328356129317993577761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14992875616344847982874029 5622328356129317993577761)
                  ·
                    refine ⟨4216746267096988495183321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5622328356129317993577761 4216746267096988495183321)
                    ·
                      refine ⟨3162559700322741371387491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216746267096988495183321 3162559700322741371387491)
                      ·
                        rfl

theorem cell23_6159063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_6159063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159063 prefixEnd_6159063 := by exact prefixLift 6159063
  have htrace : WordTrace (prefixWord ++ tailWord_6159063) baseStart_6159063 baseEnd_6159063 := by
    simpa [prefixWord, tailWord_6159063, baseEnd_6159063] using wordTrace_append hprefix tailTrace_6159063
  have hstable : (prefixWord ++ tailWord_6159063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159063).length < 2 ^ (prefixWord ++ tailWord_6159063).sum := by decide
  have hdescent : baseEnd_6159063 < baseStart_6159063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159076 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_6159076 : Nat := 118140960795 + 6159076 * 2 ^ 59
def prefixEnd_6159076 : Nat := 4983230072969 + 3 ^ 40 * 6159076 * 2
def baseEnd_6159076 : Nat := 3162566375571249820524931

theorem tailTrace_6159076 : CollatzResearch.WordTrace tailWord_6159076 prefixEnd_6159076 3162566375571249820524931 := by
  unfold tailWord_6159076
  simp only [CollatzResearch.WordTrace]
  refine ⟨112319978317363506640476541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149759971089818008853968721 112319978317363506640476541)
  ·
    refine ⟨42119991869011314990178703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112319978317363506640476541 42119991869011314990178703)
    ·
      refine ⟨63179987803516972485268055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42119991869011314990178703 63179987803516972485268055)
      ·
        refine ⟨94769981705275458727902083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63179987803516972485268055 94769981705275458727902083)
        ·
          refine ⟨142154972557913188091853125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94769981705275458727902083 142154972557913188091853125)
          ·
            refine ⟨26654057354608722767222461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142154972557913188091853125 26654057354608722767222461)
            ·
              refine ⟨9995271507978271037708423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26654057354608722767222461 9995271507978271037708423)
              ·
                refine ⟨14992907261967406556562635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9995271507978271037708423 14992907261967406556562635)
                ·
                  refine ⟨22489360892951109834843953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14992907261967406556562635 22489360892951109834843953)
                  ·
                    refine ⟨16867020669713332376132965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22489360892951109834843953 16867020669713332376132965)
                    ·
                      refine ⟨3162566375571249820524931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16867020669713332376132965 3162566375571249820524931)
                      ·
                        rfl

theorem cell23_6159076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_6159076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159076 prefixEnd_6159076 := by exact prefixLift 6159076
  have htrace : WordTrace (prefixWord ++ tailWord_6159076) baseStart_6159076 baseEnd_6159076 := by
    simpa [prefixWord, tailWord_6159076, baseEnd_6159076] using wordTrace_append hprefix tailTrace_6159076
  have hstable : (prefixWord ++ tailWord_6159076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159076).length < 2 ^ (prefixWord ++ tailWord_6159076).sum := by decide
  have hdescent : baseEnd_6159076 < baseStart_6159076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159086 : List Nat := [4, 1, 2, 1, 1, 3, 4, 7]
def baseStart_6159086 : Nat := 118140960795 + 6159086 * 2 ^ 59
def prefixEnd_6159086 : Nat := 4983230072969 + 3 ^ 40 * 6159086 * 2
def baseEnd_6159086 : Nat := 117132278162140547459255

theorem tailTrace_6159086 : CollatzResearch.WordTrace tailWord_6159086 prefixEnd_6159086 117132278162140547459255 := by
  unfold tailWord_6159086
  simp only [CollatzResearch.WordTrace]
  refine ⟨28080040170586348123602139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149760214243127189992544741 28080040170586348123602139)
  ·
    refine ⟨42120060255879522185403209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28080040170586348123602139 42120060255879522185403209)
    ·
      refine ⟨31590045191909641639052407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42120060255879522185403209 31590045191909641639052407)
      ·
        refine ⟨47385067787864462458578611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31590045191909641639052407 47385067787864462458578611)
        ·
          refine ⟨71077601681796693687867917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47385067787864462458578611 71077601681796693687867917)
          ·
            refine ⟨26654100630673760132950469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71077601681796693687867917 26654100630673760132950469)
            ·
              refine ⟨4997643868251330024928213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26654100630673760132950469 4997643868251330024928213)
              ·
                refine ⟨117132278162140547459255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4997643868251330024928213 117132278162140547459255)
                ·
                  rfl

theorem cell23_6159086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_6159086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159086 prefixEnd_6159086 := by exact prefixLift 6159086
  have htrace : WordTrace (prefixWord ++ tailWord_6159086) baseStart_6159086 baseEnd_6159086 := by
    simpa [prefixWord, tailWord_6159086, baseEnd_6159086] using wordTrace_append hprefix tailTrace_6159086
  have hstable : (prefixWord ++ tailWord_6159086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159086).length < 2 ^ (prefixWord ++ tailWord_6159086).sum := by decide
  have hdescent : baseEnd_6159086 < baseStart_6159086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159096 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 6, 1, 3]
def baseStart_6159096 : Nat := 118140960795 + 6159096 * 2 ^ 59
def prefixEnd_6159096 : Nat := 4983230072969 + 3 ^ 40 * 6159096 * 2
def baseEnd_6159096 : Nat := 3162576645184339742274839

theorem tailTrace_6159096 : CollatzResearch.WordTrace tailWord_6159096 prefixEnd_6159096 3162576645184339742274839 := by
  unfold tailWord_6159096
  simp only [CollatzResearch.WordTrace]
  refine ⟨112320343047327278348340571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149760457396436371131120761 112320343047327278348340571)
  ·
    refine ⟨168480514570990917522510857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112320343047327278348340571 168480514570990917522510857)
    ·
      refine ⟨126360385928243188141883143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168480514570990917522510857 126360385928243188141883143)
      ·
        refine ⟨189540578892364782212824715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126360385928243188141883143 189540578892364782212824715)
        ·
          refine ⟨284310868338547173319237073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189540578892364782212824715 284310868338547173319237073)
          ·
            refine ⟨213233151253910379989427805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284310868338547173319237073 213233151253910379989427805)
            ·
              refine ⟨79962431720216392496035427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213233151253910379989427805 79962431720216392496035427)
              ·
                refine ⟨119943647580324588744053141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79962431720216392496035427 119943647580324588744053141)
                ·
                  refine ⟨5622358480327715097377491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119943647580324588744053141 5622358480327715097377491)
                  ·
                    refine ⟨8433537720491572646066237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5622358480327715097377491 8433537720491572646066237)
                    ·
                      refine ⟨3162576645184339742274839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8433537720491572646066237 3162576645184339742274839)
                      ·
                        rfl

theorem cell23_6159096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_6159096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159096 prefixEnd_6159096 := by exact prefixLift 6159096
  have htrace : WordTrace (prefixWord ++ tailWord_6159096) baseStart_6159096 baseEnd_6159096 := by
    simpa [prefixWord, tailWord_6159096, baseEnd_6159096] using wordTrace_append hprefix tailTrace_6159096
  have hstable : (prefixWord ++ tailWord_6159096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159096).length < 2 ^ (prefixWord ++ tailWord_6159096).sum := by decide
  have hdescent : baseEnd_6159096 < baseStart_6159096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159119 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 4]
def baseStart_6159119 : Nat := 118140960795 + 6159119 * 2 ^ 59
def prefixEnd_6159119 : Nat := 4983230072969 + 3 ^ 40 * 6159119 * 2
def baseEnd_6159119 : Nat := 3162588455239393152287233

theorem tailTrace_6159119 : CollatzResearch.WordTrace tailWord_6159119 prefixEnd_6159119 3162588455239393152287233 := by
  unfold tailWord_6159119
  simp only [CollatzResearch.WordTrace]
  refine ⟨224641524973571231624768411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149761016649047487749845607 224641524973571231624768411)
  ·
    refine ⟨336962287460356847437152617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224641524973571231624768411 336962287460356847437152617)
    ·
      refine ⟨252721715595267635577864463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336962287460356847437152617 252721715595267635577864463)
      ·
        refine ⟨379082573392901453366796695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252721715595267635577864463 379082573392901453366796695)
        ·
          refine ⟨568623860089352180050195043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379082573392901453366796695 568623860089352180050195043)
          ·
            refine ⟨852935790134028270075292565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568623860089352180050195043 852935790134028270075292565)
            ·
              refine ⟨39981365162532575159779339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 852935790134028270075292565 39981365162532575159779339)
              ·
                refine ⟨59972047743798862739669009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39981365162532575159779339 59972047743798862739669009)
                ·
                  refine ⟨44979035807849147054751757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59972047743798862739669009 44979035807849147054751757)
                  ·
                    refine ⟨16867138427943430145531909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44979035807849147054751757 16867138427943430145531909)
                    ·
                      refine ⟨3162588455239393152287233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16867138427943430145531909 3162588455239393152287233)
                      ·
                        rfl

theorem cell23_6159119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_6159119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159119 prefixEnd_6159119 := by exact prefixLift 6159119
  have htrace : WordTrace (prefixWord ++ tailWord_6159119) baseStart_6159119 baseEnd_6159119 := by
    simpa [prefixWord, tailWord_6159119, baseEnd_6159119] using wordTrace_append hprefix tailTrace_6159119
  have hstable : (prefixWord ++ tailWord_6159119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159119).length < 2 ^ (prefixWord ++ tailWord_6159119).sum := by decide
  have hdescent : baseEnd_6159119 < baseStart_6159119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159140 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 3, 3, 2]
def baseStart_6159140 : Nat := 118140960795 + 6159140 * 2 ^ 59
def prefixEnd_6159140 : Nat := 4983230072969 + 3 ^ 40 * 6159140 * 2
def baseEnd_6159140 : Nat := 3162599238333137570124637

theorem tailTrace_6159140 : CollatzResearch.WordTrace tailWord_6159140 prefixEnd_6159140 3162599238333137570124637 := by
  unfold tailWord_6159140
  simp only [CollatzResearch.WordTrace]
  refine ⟨112321145453247576105641437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149761527270996768140855249 112321145453247576105641437)
  ·
    refine ⟨42120429544967841039615539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112321145453247576105641437 42120429544967841039615539)
    ·
      refine ⟨63180644317451761559423309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42120429544967841039615539 63180644317451761559423309)
      ·
        refine ⟨23692741619044410584783741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63180644317451761559423309 23692741619044410584783741)
        ·
          refine ⟨8884778107141653969293903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23692741619044410584783741 8884778107141653969293903)
          ·
            refine ⟨13327167160712480953940855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8884778107141653969293903 13327167160712480953940855)
            ·
              refine ⟨19990750741068721430911283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13327167160712480953940855 19990750741068721430911283)
              ·
                refine ⟨29986126111603082146366925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19990750741068721430911283 29986126111603082146366925)
                ·
                  refine ⟨11244797291851155804887597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29986126111603082146366925 11244797291851155804887597)
                  ·
                    refine ⟨4216798984444183426832849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11244797291851155804887597 4216798984444183426832849)
                    ·
                      refine ⟨3162599238333137570124637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216798984444183426832849 3162599238333137570124637)
                      ·
                        rfl

theorem cell23_6159140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_6159140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159140 prefixEnd_6159140 := by exact prefixLift 6159140
  have htrace : WordTrace (prefixWord ++ tailWord_6159140) baseStart_6159140 baseEnd_6159140 := by
    simpa [prefixWord, tailWord_6159140, baseEnd_6159140] using wordTrace_append hprefix tailTrace_6159140
  have hstable : (prefixWord ++ tailWord_6159140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159140).length < 2 ^ (prefixWord ++ tailWord_6159140).sum := by decide
  have hdescent : baseEnd_6159140 < baseStart_6159140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159153 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 1, 4, 2]
def baseStart_6159153 : Nat := 118140960795 + 6159153 * 2 ^ 59
def prefixEnd_6159153 : Nat := 4983230072969 + 3 ^ 40 * 6159153 * 2
def baseEnd_6159153 : Nat := 3162605913581646019262077

theorem tailTrace_6159153 : CollatzResearch.WordTrace tailWord_6159153 prefixEnd_6159153 3162605913581646019262077 := by
  unfold tailWord_6159153
  simp only [CollatzResearch.WordTrace]
  refine ⟨224642765055448055431506113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149761843370298703621004075 224642765055448055431506113)
  ·
    refine ⟨168482073791586041573629585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224642765055448055431506113 168482073791586041573629585)
    ·
      refine ⟨126361555343689531180222189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168482073791586041573629585 126361555343689531180222189)
      ·
        refine ⟨47385583253883574192583321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126361555343689531180222189 47385583253883574192583321)
        ·
          refine ⟨35539187440412680644437491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47385583253883574192583321 35539187440412680644437491)
          ·
            refine ⟨53308781160619020966656237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35539187440412680644437491 53308781160619020966656237)
            ·
              refine ⟨19990792935232132862496089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53308781160619020966656237 19990792935232132862496089)
              ·
                refine ⟨14993094701424099646872067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19990792935232132862496089 14993094701424099646872067)
                ·
                  refine ⟨22489642052136149470308101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14993094701424099646872067 22489642052136149470308101)
                  ·
                    refine ⟨4216807884775528025682769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22489642052136149470308101 4216807884775528025682769)
                    ·
                      refine ⟨3162605913581646019262077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216807884775528025682769 3162605913581646019262077)
                      ·
                        rfl

theorem cell23_6159153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_6159153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159153 prefixEnd_6159153 := by exact prefixLift 6159153
  have htrace : WordTrace (prefixWord ++ tailWord_6159153) baseStart_6159153 baseEnd_6159153 := by
    simpa [prefixWord, tailWord_6159153, baseEnd_6159153] using wordTrace_append hprefix tailTrace_6159153
  have hstable : (prefixWord ++ tailWord_6159153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159153).length < 2 ^ (prefixWord ++ tailWord_6159153).sum := by decide
  have hdescent : baseEnd_6159153 < baseStart_6159153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159157 : List Nat := [1, 3, 3, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_6159157 : Nat := 118140960795 + 6159157 * 2 ^ 59
def prefixEnd_6159157 : Nat := 4983230072969 + 3 ^ 40 * 6159157 * 2
def baseEnd_6159157 : Nat := 3162607967504264003612059

theorem tailTrace_6159157 : CollatzResearch.WordTrace tailWord_6159157 prefixEnd_6159157 3162607967504264003612059 := by
  unfold tailWord_6159157
  simp only [CollatzResearch.WordTrace]
  refine ⟨224642910947433564114651725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149761940631622376076434483 224642910947433564114651725)
  ·
    refine ⟨84241091605287586542994397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224642910947433564114651725 84241091605287586542994397)
    ·
      refine ⟨31590409351982844953622899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84241091605287586542994397 31590409351982844953622899)
      ·
        refine ⟨47385614027974267430434349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31590409351982844953622899 47385614027974267430434349)
        ·
          refine ⟨17769605260490350286412881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47385614027974267430434349 17769605260490350286412881)
          ·
            refine ⟨13327203945367762714809661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17769605260490350286412881 13327203945367762714809661)
            ·
              refine ⟨4997701479512911018053623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13327203945367762714809661 4997701479512911018053623)
              ·
                refine ⟨7496552219269366527080435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997701479512911018053623 7496552219269366527080435)
                ·
                  refine ⟨11244828328904049790620653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7496552219269366527080435 11244828328904049790620653)
                  ·
                    refine ⟨4216810623339018671482745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11244828328904049790620653 4216810623339018671482745)
                    ·
                      refine ⟨3162607967504264003612059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216810623339018671482745 3162607967504264003612059)
                      ·
                        rfl

theorem cell23_6159157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_6159157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159157 prefixEnd_6159157 := by exact prefixLift 6159157
  have htrace : WordTrace (prefixWord ++ tailWord_6159157) baseStart_6159157 baseEnd_6159157 := by
    simpa [prefixWord, tailWord_6159157, baseEnd_6159157] using wordTrace_append hprefix tailTrace_6159157
  have hstable : (prefixWord ++ tailWord_6159157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159157).length < 2 ^ (prefixWord ++ tailWord_6159157).sum := by decide
  have hdescent : baseEnd_6159157 < baseStart_6159157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159226 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_6159226 : Nat := 118140960795 + 6159226 * 2 ^ 59
def prefixEnd_6159226 : Nat := 4983230072969 + 3 ^ 40 * 6159226 * 2
def baseEnd_6159226 : Nat := 3162643397669424233649241

theorem tailTrace_6159226 : CollatzResearch.WordTrace tailWord_6159226 prefixEnd_6159226 3162643397669424233649241 := by
  unfold tailWord_6159226
  simp only [CollatzResearch.WordTrace]
  refine ⟨56161356896045897224728383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149763618389455725932609021 56161356896045897224728383)
  ·
    refine ⟨84242035344068845837092575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56161356896045897224728383 84242035344068845837092575)
    ·
      refine ⟨126363053016103268755638863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84242035344068845837092575 126363053016103268755638863)
      ·
        refine ⟨189544579524154903133458295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126363053016103268755638863 189544579524154903133458295)
        ·
          refine ⟨284316869286232354700187443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189544579524154903133458295 284316869286232354700187443)
          ·
            refine ⟨426475303929348532050281165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284316869286232354700187443 426475303929348532050281165)
            ·
              refine ⟨159928238973505699518855437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426475303929348532050281165 159928238973505699518855437)
              ·
                refine ⟨59973089615064637319570789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159928238973505699518855437 59973089615064637319570789)
                ·
                  refine ⟨11244954302824619497419523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59973089615064637319570789 11244954302824619497419523)
                  ·
                    refine ⟨16867431454236929246129285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11244954302824619497419523 16867431454236929246129285)
                    ·
                      refine ⟨3162643397669424233649241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16867431454236929246129285 3162643397669424233649241)
                      ·
                        rfl

theorem cell23_6159226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_6159226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159226 prefixEnd_6159226 := by exact prefixLift 6159226
  have htrace : WordTrace (prefixWord ++ tailWord_6159226) baseStart_6159226 baseEnd_6159226 := by
    simpa [prefixWord, tailWord_6159226, baseEnd_6159226] using wordTrace_append hprefix tailTrace_6159226
  have hstable : (prefixWord ++ tailWord_6159226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159226).length < 2 ^ (prefixWord ++ tailWord_6159226).sum := by decide
  have hdescent : baseEnd_6159226 < baseStart_6159226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159243 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 2, 4, 2]
def baseStart_6159243 : Nat := 118140960795 + 6159243 * 2 ^ 59
def prefixEnd_6159243 : Nat := 4983230072969 + 3 ^ 40 * 6159243 * 2
def baseEnd_6159243 : Nat := 3162652126840550667136663

theorem tailTrace_6159243 : CollatzResearch.WordTrace tailWord_6159243 prefixEnd_6159243 3162652126840550667136663 := by
  unfold tailWord_6159243
  simp only [CollatzResearch.WordTrace]
  refine ⟨224646047625122000802282383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149764031750081333868188255 224646047625122000802282383)
  ·
    refine ⟨336969071437683001203423575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224646047625122000802282383 336969071437683001203423575)
    ·
      refine ⟨505453607156524501805135363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336969071437683001203423575 505453607156524501805135363)
      ·
        refine ⟨758180410734786752707703045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505453607156524501805135363 758180410734786752707703045)
        ·
          refine ⟨142158827012772516132694321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 758180410734786752707703045 142158827012772516132694321)
          ·
            refine ⟨106619120259579387099520741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142158827012772516132694321 106619120259579387099520741)
            ·
              refine ⟨19991085048671135081160139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106619120259579387099520741 19991085048671135081160139)
              ·
                refine ⟨29986627573006702621740209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19991085048671135081160139 29986627573006702621740209)
                ·
                  refine ⟨22489970679755026966305157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29986627573006702621740209 22489970679755026966305157)
                  ·
                    refine ⟨4216869502454067556182217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22489970679755026966305157 4216869502454067556182217)
                    ·
                      refine ⟨3162652126840550667136663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216869502454067556182217 3162652126840550667136663)
                      ·
                        rfl

theorem cell23_6159243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 4, 2].length) (baseStart_6159243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159243 prefixEnd_6159243 := by exact prefixLift 6159243
  have htrace : WordTrace (prefixWord ++ tailWord_6159243) baseStart_6159243 baseEnd_6159243 := by
    simpa [prefixWord, tailWord_6159243, baseEnd_6159243] using wordTrace_append hprefix tailTrace_6159243
  have hstable : (prefixWord ++ tailWord_6159243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159243).length < 2 ^ (prefixWord ++ tailWord_6159243).sum := by decide
  have hdescent : baseEnd_6159243 < baseStart_6159243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159253 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 3, 4]
def baseStart_6159253 : Nat := 118140960795 + 6159253 * 2 ^ 59
def prefixEnd_6159253 : Nat := 4983230072969 + 3 ^ 40 * 6159253 * 2
def baseEnd_6159253 : Nat := 1054219087215698542670539

theorem tailTrace_6159253 : CollatzResearch.WordTrace tailWord_6159253 prefixEnd_6159253 1054219087215698542670539 := by
  unfold tailWord_6159253
  simp only [CollatzResearch.WordTrace]
  refine ⟨224646412355085772510146413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149764274903390515006764275 224646412355085772510146413)
  ·
    refine ⟨84242404633157164691304905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224646412355085772510146413 84242404633157164691304905)
    ·
      refine ⟨63181803474867873518478679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84242404633157164691304905 63181803474867873518478679)
      ·
        refine ⟨94772705212301810277718019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63181803474867873518478679 94772705212301810277718019)
        ·
          refine ⟨142159057818452715416577029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94772705212301810277718019 142159057818452715416577029)
          ·
            refine ⟨26654823340959884140608193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142159057818452715416577029 26654823340959884140608193)
            ·
              refine ⟨19991117505719913105456145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26654823340959884140608193 19991117505719913105456145)
              ·
                refine ⟨14993338129289934829092109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19991117505719913105456145 14993338129289934829092109)
                ·
                  refine ⟨5622501798483725560909541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14993338129289934829092109 5622501798483725560909541)
                  ·
                    refine ⟨1054219087215698542670539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5622501798483725560909541 1054219087215698542670539)
                    ·
                      rfl

theorem cell23_6159253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_6159253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159253 prefixEnd_6159253 := by exact prefixLift 6159253
  have htrace : WordTrace (prefixWord ++ tailWord_6159253) baseStart_6159253 baseEnd_6159253 := by
    simpa [prefixWord, tailWord_6159253, baseEnd_6159253] using wordTrace_append hprefix tailTrace_6159253
  have hstable : (prefixWord ++ tailWord_6159253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159253).length < 2 ^ (prefixWord ++ tailWord_6159253).sum := by decide
  have hdescent : baseEnd_6159253 < baseStart_6159253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159263 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 3]
def baseStart_6159263 : Nat := 118140960795 + 6159263 * 2 ^ 59
def prefixEnd_6159263 : Nat := 4983230072969 + 3 ^ 40 * 6159263 * 2
def baseEnd_6159263 : Nat := 3162662396453640588886571

theorem tailTrace_6159263 : CollatzResearch.WordTrace tailWord_6159263 prefixEnd_6159263 3162662396453640588886571 := by
  unfold tailWord_6159263
  simp only [CollatzResearch.WordTrace]
  refine ⟨224646777085049544218010443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149764518056699696145340295 224646777085049544218010443)
  ·
    refine ⟨336970165627574316327015665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224646777085049544218010443 336970165627574316327015665)
    ·
      refine ⟨252727624220680737245261749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336970165627574316327015665 252727624220680737245261749)
      ·
        refine ⟨23693214770688819116743289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 252727624220680737245261749 23693214770688819116743289)
        ·
          refine ⟨17769911078016614337557467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23693214770688819116743289 17769911078016614337557467)
          ·
            refine ⟨26654866617024921506336201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17769911078016614337557467 26654866617024921506336201)
            ·
              refine ⟨19991149962768691129752151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26654866617024921506336201 19991149962768691129752151)
              ·
                refine ⟨29986724944153036694628227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19991149962768691129752151 29986724944153036694628227)
                ·
                  refine ⟨44980087416229555041942341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29986724944153036694628227 44980087416229555041942341)
                  ·
                    refine ⟨8433766390543041570364189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44980087416229555041942341 8433766390543041570364189)
                    ·
                      refine ⟨3162662396453640588886571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8433766390543041570364189 3162662396453640588886571)
                      ·
                        rfl

theorem cell23_6159263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_6159263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159263 prefixEnd_6159263 := by exact prefixLift 6159263
  have htrace : WordTrace (prefixWord ++ tailWord_6159263) baseStart_6159263 baseEnd_6159263 := by
    simpa [prefixWord, tailWord_6159263, baseEnd_6159263] using wordTrace_append hprefix tailTrace_6159263
  have hstable : (prefixWord ++ tailWord_6159263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159263).length < 2 ^ (prefixWord ++ tailWord_6159263).sum := by decide
  have hdescent : baseEnd_6159263 < baseStart_6159263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159276 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 3]
def baseStart_6159276 : Nat := 118140960795 + 6159276 * 2 ^ 59
def prefixEnd_6159276 : Nat := 4983230072969 + 3 ^ 40 * 6159276 * 2
def baseEnd_6159276 : Nat := 3162669071702149038024011

theorem tailTrace_6159276 : CollatzResearch.WordTrace tailWord_6159276 prefixEnd_6159276 3162669071702149038024011 := by
  unfold tailWord_6159276
  simp only [CollatzResearch.WordTrace]
  refine ⟨112323625617001223719116841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149764834156001631625489121 112323625617001223719116841)
  ·
    refine ⟨84242719212750917789337631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112323625617001223719116841 84242719212750917789337631)
    ·
      refine ⟨126364078819126376684006447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84242719212750917789337631 126364078819126376684006447)
      ·
        refine ⟨189546118228689565026009671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126364078819126376684006447 189546118228689565026009671)
        ·
          refine ⟨284319177343034347539014507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189546118228689565026009671 284319177343034347539014507)
          ·
            refine ⟨426478766014551521308521761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284319177343034347539014507 426478766014551521308521761)
            ·
              refine ⟨319859074510913640981391321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426478766014551521308521761 319859074510913640981391321)
              ·
                refine ⟨239894305883185230736043491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319859074510913640981391321 239894305883185230736043491)
                ·
                  refine ⟨359841458824777846104065237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239894305883185230736043491 359841458824777846104065237)
                  ·
                    refine ⟨8433784191205730768064029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 359841458824777846104065237 8433784191205730768064029)
                    ·
                      refine ⟨3162669071702149038024011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8433784191205730768064029 3162669071702149038024011)
                      ·
                        rfl

theorem cell23_6159276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_6159276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159276 prefixEnd_6159276 := by exact prefixLift 6159276
  have htrace : WordTrace (prefixWord ++ tailWord_6159276) baseStart_6159276 baseEnd_6159276 := by
    simpa [prefixWord, tailWord_6159276, baseEnd_6159276] using wordTrace_append hprefix tailTrace_6159276
  have hstable : (prefixWord ++ tailWord_6159276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159276).length < 2 ^ (prefixWord ++ tailWord_6159276).sum := by decide
  have hdescent : baseEnd_6159276 < baseStart_6159276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159277 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6159277 : Nat := 118140960795 + 6159277 * 2 ^ 59
def prefixEnd_6159277 : Nat := 4983230072969 + 3 ^ 40 * 6159277 * 2
def baseEnd_6159277 : Nat := 3162669585182803534111507

theorem tailTrace_6159277 : CollatzResearch.WordTrace tailWord_6159277 prefixEnd_6159277 3162669585182803534111507 := by
  unfold tailWord_6159277
  simp only [CollatzResearch.WordTrace]
  refine ⟨224647287706998824609020085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149764858471332549739346723 224647287706998824609020085)
  ·
    refine ⟨21060683222531139807095633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224647287706998824609020085 21060683222531139807095633)
    ·
      refine ⟨15795512416898354855321725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21060683222531139807095633 15795512416898354855321725)
      ·
        refine ⟨5923317156336883070745647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15795512416898354855321725 5923317156336883070745647)
        ·
          refine ⟨8884975734505324606118471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5923317156336883070745647 8884975734505324606118471)
          ·
            refine ⟨13327463601757986909177707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8884975734505324606118471 13327463601757986909177707)
            ·
              refine ⟨19991195402636980363766561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13327463601757986909177707 19991195402636980363766561)
              ·
                refine ⟨14993396551977735272824921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19991195402636980363766561 14993396551977735272824921)
                ·
                  refine ⟨11245047413983301454618691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14993396551977735272824921 11245047413983301454618691)
                  ·
                    refine ⟨16867571120974952181928037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11245047413983301454618691 16867571120974952181928037)
                    ·
                      refine ⟨3162669585182803534111507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16867571120974952181928037 3162669585182803534111507)
                      ·
                        rfl

theorem cell23_6159277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6159277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159277 prefixEnd_6159277 := by exact prefixLift 6159277
  have htrace : WordTrace (prefixWord ++ tailWord_6159277) baseStart_6159277 baseEnd_6159277 := by
    simpa [prefixWord, tailWord_6159277, baseEnd_6159277] using wordTrace_append hprefix tailTrace_6159277
  have hstable : (prefixWord ++ tailWord_6159277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159277).length < 2 ^ (prefixWord ++ tailWord_6159277).sum := by decide
  have hdescent : baseEnd_6159277 < baseStart_6159277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159303 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 3, 5, 2]
def baseStart_6159303 : Nat := 118140960795 + 6159303 * 2 ^ 59
def prefixEnd_6159303 : Nat := 4983230072969 + 3 ^ 40 * 6159303 * 2
def baseEnd_6159303 : Nat := 3162682935679820432386387

theorem tailTrace_6159303 : CollatzResearch.WordTrace tailWord_6159303 prefixEnd_6159303 3162682935679820432386387 := by
  unfold tailWord_6159303
  simp only [CollatzResearch.WordTrace]
  refine ⟨224648236004904631049466563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149765490669936420699644375 224648236004904631049466563)
  ·
    refine ⟨336972354007356946574199845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224648236004904631049466563 336972354007356946574199845)
    ·
      refine ⟨63182316376379427482662471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336972354007356946574199845 63182316376379427482662471)
      ·
        refine ⟨94773474564569141223993707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63182316376379427482662471 94773474564569141223993707)
        ·
          refine ⟨142160211846853711835990561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94773474564569141223993707 142160211846853711835990561)
          ·
            refine ⟨106620158885140283876992921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142160211846853711835990561 106620158885140283876992921)
            ·
              refine ⟨79965119163855212907744691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106620158885140283876992921 79965119163855212907744691)
              ·
                refine ⟨119947678745782819361617037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79965119163855212907744691 119947678745782819361617037)
                ·
                  refine ⟨44980379529668557260606389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119947678745782819361617037 44980379529668557260606389)
                  ·
                    refine ⟨4216910580906427243181849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44980379529668557260606389 4216910580906427243181849)
                    ·
                      refine ⟨3162682935679820432386387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216910580906427243181849 3162682935679820432386387)
                      ·
                        rfl

theorem cell23_6159303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_6159303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159303 prefixEnd_6159303 := by exact prefixLift 6159303
  have htrace : WordTrace (prefixWord ++ tailWord_6159303) baseStart_6159303 baseEnd_6159303 := by
    simpa [prefixWord, tailWord_6159303, baseEnd_6159303] using wordTrace_append hprefix tailTrace_6159303
  have hstable : (prefixWord ++ tailWord_6159303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159303).length < 2 ^ (prefixWord ++ tailWord_6159303).sum := by decide
  have hdescent : baseEnd_6159303 < baseStart_6159303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159320 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 2, 3, 2]
def baseStart_6159320 : Nat := 118140960795 + 6159320 * 2 ^ 59
def prefixEnd_6159320 : Nat := 4983230072969 + 3 ^ 40 * 6159320 * 2
def baseEnd_6159320 : Nat := 3162691664850946865873809

theorem tailTrace_6159320 : CollatzResearch.WordTrace tailWord_6159320 prefixEnd_6159320 3162691664850946865873809 := by
  unfold tailWord_6159320
  simp only [CollatzResearch.WordTrace]
  refine ⟨112324428022921521476417707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149765904030562028635223609 112324428022921521476417707)
  ·
    refine ⟨168486642034382282214626561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112324428022921521476417707 168486642034382282214626561)
    ·
      refine ⟨126364981525786711660969921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168486642034382282214626561 126364981525786711660969921)
      ·
        refine ⟨94773736144340033745727441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126364981525786711660969921 94773736144340033745727441)
        ·
          refine ⟨71080302108255025309295581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94773736144340033745727441 71080302108255025309295581)
          ·
            refine ⟨26655113290595634490985843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71080302108255025309295581 26655113290595634490985843)
            ·
              refine ⟨39982669935893451736478765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26655113290595634490985843 39982669935893451736478765)
              ·
                refine ⟨14993501225960044401179537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39982669935893451736478765 14993501225960044401179537)
                ·
                  refine ⟨11245125919470033300884653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14993501225960044401179537 11245125919470033300884653)
                  ·
                    refine ⟨4216922219801262487831745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11245125919470033300884653 4216922219801262487831745)
                    ·
                      refine ⟨3162691664850946865873809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216922219801262487831745 3162691664850946865873809)
                      ·
                        rfl

theorem cell23_6159320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_6159320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159320 prefixEnd_6159320 := by exact prefixLift 6159320
  have htrace : WordTrace (prefixWord ++ tailWord_6159320) baseStart_6159320 baseEnd_6159320 := by
    simpa [prefixWord, tailWord_6159320, baseEnd_6159320] using wordTrace_append hprefix tailTrace_6159320
  have hstable : (prefixWord ++ tailWord_6159320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159320).length < 2 ^ (prefixWord ++ tailWord_6159320).sum := by decide
  have hdescent : baseEnd_6159320 < baseStart_6159320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159350 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_6159350 : Nat := 118140960795 + 6159350 * 2 ^ 59
def prefixEnd_6159350 : Nat := 4983230072969 + 3 ^ 40 * 6159350 * 2
def baseEnd_6159350 : Nat := 3162707069270581748498671

theorem tailTrace_6159350 : CollatzResearch.WordTrace tailWord_6159350 prefixEnd_6159350 3162707069270581748498671 := by
  unfold tailWord_6159350
  simp only [CollatzResearch.WordTrace]
  refine ⟨14040621889733397379776719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149766633490489572050951669 14040621889733397379776719)
  ·
    refine ⟨21060932834600096069665079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14040621889733397379776719 21060932834600096069665079)
    ·
      refine ⟨31591399251900144104497619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21060932834600096069665079 31591399251900144104497619)
      ·
        refine ⟨47387098877850216156746429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31591399251900144104497619 47387098877850216156746429)
        ·
          refine ⟨17770162079193831058779911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47387098877850216156746429 17770162079193831058779911)
          ·
            refine ⟨26655243118790746588169867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17770162079193831058779911 26655243118790746588169867)
            ·
              refine ⟨39982864678186119882254801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26655243118790746588169867 39982864678186119882254801)
              ·
                refine ⟨29987148508639589911691101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39982864678186119882254801 29987148508639589911691101)
                ·
                  refine ⟨11245180690739846216884163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29987148508639589911691101 11245180690739846216884163)
                  ·
                    refine ⟨16867771036109769325326245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11245180690739846216884163 16867771036109769325326245)
                    ·
                      refine ⟨3162707069270581748498671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16867771036109769325326245 3162707069270581748498671)
                      ·
                        rfl

theorem cell23_6159350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_6159350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159350 prefixEnd_6159350 := by exact prefixLift 6159350
  have htrace : WordTrace (prefixWord ++ tailWord_6159350) baseStart_6159350 baseEnd_6159350 := by
    simpa [prefixWord, tailWord_6159350, baseEnd_6159350] using wordTrace_append hprefix tailTrace_6159350
  have hstable : (prefixWord ++ tailWord_6159350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159350).length < 2 ^ (prefixWord ++ tailWord_6159350).sum := by decide
  have hdescent : baseEnd_6159350 < baseStart_6159350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159353 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 5, 2, 3]
def baseStart_6159353 : Nat := 118140960795 + 6159353 * 2 ^ 59
def prefixEnd_6159353 : Nat := 4983230072969 + 3 ^ 40 * 6159353 * 2
def baseEnd_6159353 : Nat := 3162708609712545236761157

theorem tailTrace_6159353 : CollatzResearch.WordTrace tailWord_6159353 prefixEnd_6159353 3162708609712545236761157 := by
  unfold tailWord_6159353
  simp only [CollatzResearch.WordTrace]
  refine ⟨224650059654723489588786713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149766706436482326392524475 224650059654723489588786713)
  ·
    refine ⟨168487544741042617191590035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224650059654723489588786713 168487544741042617191590035)
    ·
      refine ⟨252731317111563925787385053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168487544741042617191590035 252731317111563925787385053)
      ·
        refine ⟨94774243916836472170269395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252731317111563925787385053 94774243916836472170269395)
        ·
          refine ⟨142161365875254708255404093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94774243916836472170269395 142161365875254708255404093)
          ·
            refine ⟨53310512203220515595776535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142161365875254708255404093 53310512203220515595776535)
            ·
              refine ⟨79965768304830773393664803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53310512203220515595776535 79965768304830773393664803)
              ·
                refine ⟨119948652457246160090497205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79965768304830773393664803 119948652457246160090497205)
                ·
                  refine ⟨11245186167866827508484113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119948652457246160090497205 11245186167866827508484113)
                  ·
                    refine ⟨8433889625900120631363085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11245186167866827508484113 8433889625900120631363085)
                    ·
                      refine ⟨3162708609712545236761157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8433889625900120631363085 3162708609712545236761157)
                      ·
                        rfl

theorem cell23_6159353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_6159353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159353 prefixEnd_6159353 := by exact prefixLift 6159353
  have htrace : WordTrace (prefixWord ++ tailWord_6159353) baseStart_6159353 baseEnd_6159353 := by
    simpa [prefixWord, tailWord_6159353, baseEnd_6159353] using wordTrace_append hprefix tailTrace_6159353
  have hstable : (prefixWord ++ tailWord_6159353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159353).length < 2 ^ (prefixWord ++ tailWord_6159353).sum := by decide
  have hdescent : baseEnd_6159353 < baseStart_6159353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159367 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 3, 2, 2]
def baseStart_6159367 : Nat := 118140960795 + 6159367 * 2 ^ 59
def prefixEnd_6159367 : Nat := 4983230072969 + 3 ^ 40 * 6159367 * 2
def baseEnd_6159367 : Nat := 3162715798441708181986093

theorem tailTrace_6159367 : CollatzResearch.WordTrace tailWord_6159367 prefixEnd_6159367 3162715798441708181986093 := by
  unfold tailWord_6159367
  simp only [CollatzResearch.WordTrace]
  refine ⟨224650570276672769979796355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149767046851115179986530903 224650570276672769979796355)
  ·
    refine ⟨336975855415009154969694533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224650570276672769979796355 336975855415009154969694533)
    ·
      refine ⟨63182972890314216556817725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336975855415009154969694533 63182972890314216556817725)
      ·
        refine ⟨23693614833867831208806647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63182972890314216556817725 23693614833867831208806647)
        ·
          refine ⟨35540422250801746813209971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23693614833867831208806647 35540422250801746813209971)
          ·
            refine ⟨53310633376202620219814957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35540422250801746813209971 53310633376202620219814957)
            ·
              refine ⟨19991487516075982582430609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53310633376202620219814957 19991487516075982582430609)
              ·
                refine ⟨14993615637056986936822957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19991487516075982582430609 14993615637056986936822957)
                ·
                  refine ⟨5622605863896370101308609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14993615637056986936822957 5622605863896370101308609)
                  ·
                    refine ⟨4216954397922277575981457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5622605863896370101308609 4216954397922277575981457)
                    ·
                      refine ⟨3162715798441708181986093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216954397922277575981457 3162715798441708181986093)
                      ·
                        rfl

theorem cell23_6159367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_6159367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159367 prefixEnd_6159367 := by exact prefixLift 6159367
  have htrace : WordTrace (prefixWord ++ tailWord_6159367) baseStart_6159367 baseEnd_6159367 := by
    simpa [prefixWord, tailWord_6159367, baseEnd_6159367] using wordTrace_append hprefix tailTrace_6159367
  have hstable : (prefixWord ++ tailWord_6159367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159367).length < 2 ^ (prefixWord ++ tailWord_6159367).sum := by decide
  have hdescent : baseEnd_6159367 < baseStart_6159367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159370 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_6159370 : Nat := 118140960795 + 6159370 * 2 ^ 59
def prefixEnd_6159370 : Nat := 4983230072969 + 3 ^ 40 * 6159370 * 2
def baseEnd_6159370 : Nat := 3162717338883671670248579

theorem tailTrace_6159370 : CollatzResearch.WordTrace tailWord_6159370 prefixEnd_6159370 3162717338883671670248579 := by
  unfold tailWord_6159370
  simp only [CollatzResearch.WordTrace]
  refine ⟨56162669923915475373038891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149767119797107934328103709 56162669923915475373038891)
  ·
    refine ⟨84244004885873213059558337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56162669923915475373038891 84244004885873213059558337)
    ·
      refine ⟨63183003664404909794668753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84244004885873213059558337 63183003664404909794668753)
      ·
        refine ⟨47387252748303682346001565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63183003664404909794668753 47387252748303682346001565)
        ·
          refine ⟨17770219780613880879750587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47387252748303682346001565 17770219780613880879750587)
          ·
            refine ⟨26655329670920821319625881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17770219780613880879750587 26655329670920821319625881)
            ·
              refine ⟨19991497253190615989719411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26655329670920821319625881 19991497253190615989719411)
              ·
                refine ⟨29987245879785923984579117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19991497253190615989719411 29987245879785923984579117)
                ·
                  refine ⟨11245217204919721494217169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29987245879785923984579117 11245217204919721494217169)
                  ·
                    refine ⟨8433912903689791120662877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11245217204919721494217169 8433912903689791120662877)
                    ·
                      refine ⟨3162717338883671670248579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8433912903689791120662877 3162717338883671670248579)
                      ·
                        rfl

theorem cell23_6159370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_6159370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159370 prefixEnd_6159370 := by exact prefixLift 6159370
  have htrace : WordTrace (prefixWord ++ tailWord_6159370) baseStart_6159370 baseEnd_6159370 := by
    simpa [prefixWord, tailWord_6159370, baseEnd_6159370] using wordTrace_append hprefix tailTrace_6159370
  have hstable : (prefixWord ++ tailWord_6159370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159370).length < 2 ^ (prefixWord ++ tailWord_6159370).sum := by decide
  have hdescent : baseEnd_6159370 < baseStart_6159370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159384 : List Nat := [2, 1, 2, 3, 2, 2, 1, 5, 1, 2, 2]
def baseStart_6159384 : Nat := 118140960795 + 6159384 * 2 ^ 59
def prefixEnd_6159384 : Nat := 4983230072969 + 3 ^ 40 * 6159384 * 2
def baseEnd_6159384 : Nat := 3162724527612834615473515

theorem tailTrace_6159384 : CollatzResearch.WordTrace tailWord_6159384 prefixEnd_6159384 3162724527612834615473515 := by
  unfold tailWord_6159384
  simp only [CollatzResearch.WordTrace]
  refine ⟨112325595158805590941582603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149767460211740787922110137 112325595158805590941582603)
  ·
    refine ⟨168488392738208386412373905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112325595158805590941582603 168488392738208386412373905)
    ·
      refine ⟨126366294553656289809280429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168488392738208386412373905 126366294553656289809280429)
      ·
        refine ⟨47387360457621108678480161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126366294553656289809280429 47387360457621108678480161)
        ·
          refine ⟨35540520343215831508860121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47387360457621108678480161 35540520343215831508860121)
          ·
            refine ⟨26655390257411873631645091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35540520343215831508860121 26655390257411873631645091)
            ·
              refine ⟨39983085386117810447467637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26655390257411873631645091 39983085386117810447467637)
              ·
                refine ⟨3748414254948544729450091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39983085386117810447467637 3748414254948544729450091)
                ·
                  refine ⟨5622621382422817094175137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3748414254948544729450091 5622621382422817094175137)
                  ·
                    refine ⟨4216966036817112820631353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5622621382422817094175137 4216966036817112820631353)
                    ·
                      refine ⟨3162724527612834615473515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216966036817112820631353 3162724527612834615473515)
                      ·
                        rfl

theorem cell23_6159384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_6159384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159384 prefixEnd_6159384 := by exact prefixLift 6159384
  have htrace : WordTrace (prefixWord ++ tailWord_6159384) baseStart_6159384 baseEnd_6159384 := by
    simpa [prefixWord, tailWord_6159384, baseEnd_6159384] using wordTrace_append hprefix tailTrace_6159384
  have hstable : (prefixWord ++ tailWord_6159384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159384).length < 2 ^ (prefixWord ++ tailWord_6159384).sum := by decide
  have hdescent : baseEnd_6159384 < baseStart_6159384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159417 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 1, 3, 3]
def baseStart_6159417 : Nat := 118140960795 + 6159417 * 2 ^ 59
def prefixEnd_6159417 : Nat := 4983230072969 + 3 ^ 40 * 6159417 * 2
def baseEnd_6159417 : Nat := 3162741472474432986360863

theorem tailTrace_6159417 : CollatzResearch.WordTrace tailWord_6159417 prefixEnd_6159417 3162741472474432986360863 := by
  unfold tailWord_6159417
  simp only [CollatzResearch.WordTrace]
  refine ⟨224652393926491628519116505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149768262617661085679411003 224652393926491628519116505)
  ·
    refine ⟨168489295444868721389337379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224652393926491628519116505 168489295444868721389337379)
    ·
      refine ⟨252733943167303082084006069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168489295444868721389337379 252733943167303082084006069)
      ·
        refine ⟨23693807171934663945375569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 252733943167303082084006069 23693807171934663945375569)
        ·
          refine ⟨17770355378950997959031677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23693807171934663945375569 17770355378950997959031677)
          ·
            refine ⟨6663883267106624234636879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17770355378950997959031677 6663883267106624234636879)
            ·
              refine ⟨9995824900659936351955319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6663883267106624234636879 9995824900659936351955319)
              ·
                refine ⟨14993737350989904527932979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9995824900659936351955319 14993737350989904527932979)
                ·
                  refine ⟨22490606026484856791899469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14993737350989904527932979 22490606026484856791899469)
                  ·
                    refine ⟨8433977259931821296962301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22490606026484856791899469 8433977259931821296962301)
                    ·
                      refine ⟨3162741472474432986360863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8433977259931821296962301 3162741472474432986360863)
                      ·
                        rfl

theorem cell23_6159417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_6159417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159417 prefixEnd_6159417 := by exact prefixLift 6159417
  have htrace : WordTrace (prefixWord ++ tailWord_6159417) baseStart_6159417 baseEnd_6159417 := by
    simpa [prefixWord, tailWord_6159417, baseEnd_6159417] using wordTrace_append hprefix tailTrace_6159417
  have hstable : (prefixWord ++ tailWord_6159417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159417).length < 2 ^ (prefixWord ++ tailWord_6159417).sum := by decide
  have hdescent : baseEnd_6159417 < baseStart_6159417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159427 : List Nat := [1, 1, 1, 3, 1, 2, 6, 2, 1, 3, 2]
def baseStart_6159427 : Nat := 118140960795 + 6159427 * 2 ^ 59
def prefixEnd_6159427 : Nat := 4983230072969 + 3 ^ 40 * 6159427 * 2
def baseEnd_6159427 : Nat := 3162746607280977947235817

theorem tailTrace_6159427 : CollatzResearch.WordTrace tailWord_6159427 prefixEnd_6159427 3162746607280977947235817 := by
  unfold tailWord_6159427
  simp only [CollatzResearch.WordTrace]
  refine ⟨224652758656455400226980535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149768505770970266817987023 224652758656455400226980535)
  ·
    refine ⟨336979137984683100340470803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224652758656455400226980535 336979137984683100340470803)
    ·
      refine ⟨505468706977024650510706205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336979137984683100340470803 505468706977024650510706205)
      ·
        refine ⟨189550765116384243941514827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 505468706977024650510706205 189550765116384243941514827)
        ·
          refine ⟨284326147674576365912272241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189550765116384243941514827 284326147674576365912272241)
          ·
            refine ⟨213244610755932274434204181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284326147674576365912272241 213244610755932274434204181)
            ·
              refine ⟨9995841129184325364103321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 213244610755932274434204181 9995841129184325364103321)
              ·
                refine ⟨7496880846888244023077491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9995841129184325364103321 7496880846888244023077491)
                ·
                  refine ⟨11245321270332366034616237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7496880846888244023077491 11245321270332366034616237)
                  ·
                    refine ⟨4216995476374637262981089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11245321270332366034616237 4216995476374637262981089)
                    ·
                      refine ⟨3162746607280977947235817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4216995476374637262981089 3162746607280977947235817)
                      ·
                        rfl

theorem cell23_6159427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 3, 2].length) (baseStart_6159427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159427 prefixEnd_6159427 := by exact prefixLift 6159427
  have htrace : WordTrace (prefixWord ++ tailWord_6159427) baseStart_6159427 baseEnd_6159427 := by
    simpa [prefixWord, tailWord_6159427, baseEnd_6159427] using wordTrace_append hprefix tailTrace_6159427
  have hstable : (prefixWord ++ tailWord_6159427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159427).length < 2 ^ (prefixWord ++ tailWord_6159427).sum := by decide
  have hdescent : baseEnd_6159427 < baseStart_6159427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159440 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 1, 4, 2]
def baseStart_6159440 : Nat := 118140960795 + 6159440 * 2 ^ 59
def prefixEnd_6159440 : Nat := 4983230072969 + 3 ^ 40 * 6159440 * 2
def baseEnd_6159440 : Nat := 3162753282529486396373257

theorem tailTrace_6159440 : CollatzResearch.WordTrace tailWord_6159440 prefixEnd_6159440 3162753282529486396373257 := by
  unfold tailWord_6159440
  simp only [CollatzResearch.WordTrace]
  refine ⟨112326616402704151723601887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149768821870272202298135849 112326616402704151723601887)
  ·
    refine ⟨168489924604056227585402831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112326616402704151723601887 168489924604056227585402831)
    ·
      refine ⟨252734886906084341378104247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168489924604056227585402831 252734886906084341378104247)
      ·
        refine ⟨379102330359126512067156371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252734886906084341378104247 379102330359126512067156371)
        ·
          refine ⟨568653495538689768100734557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379102330359126512067156371 568653495538689768100734557)
          ·
            refine ⟨213245060827008663037775459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 568653495538689768100734557 213245060827008663037775459)
            ·
              refine ⟨319867591240512994556663189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213245060827008663037775459 319867591240512994556663189)
              ·
                refine ⟨14993793339399046619843587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 319867591240512994556663189 14993793339399046619843587)
                ·
                  refine ⟨22490690009098569929765381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14993793339399046619843587 22490690009098569929765381)
                  ·
                    refine ⟨4217004376705981861831009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22490690009098569929765381 4217004376705981861831009)
                    ·
                      refine ⟨3162753282529486396373257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4217004376705981861831009 3162753282529486396373257)
                      ·
                        rfl

theorem cell23_6159440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 4, 2].length) (baseStart_6159440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159440 prefixEnd_6159440 := by exact prefixLift 6159440
  have htrace : WordTrace (prefixWord ++ tailWord_6159440) baseStart_6159440 baseEnd_6159440 := by
    simpa [prefixWord, tailWord_6159440, baseEnd_6159440] using wordTrace_append hprefix tailTrace_6159440
  have hstable : (prefixWord ++ tailWord_6159440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159440).length < 2 ^ (prefixWord ++ tailWord_6159440).sum := by decide
  have hdescent : baseEnd_6159440 < baseStart_6159440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159457 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 4, 2, 2]
def baseStart_6159457 : Nat := 118140960795 + 6159457 * 2 ^ 59
def prefixEnd_6159457 : Nat := 4983230072969 + 3 ^ 40 * 6159457 * 2
def baseEnd_6159457 : Nat := 3162762011700612829860679

theorem tailTrace_6159457 : CollatzResearch.WordTrace tailWord_6159457 prefixEnd_6159457 3162762011700612829860679 := by
  unfold tailWord_6159457
  simp only [CollatzResearch.WordTrace]
  refine ⟨224653852846346715350572625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149769235230897810233715083 224653852846346715350572625)
  ·
    refine ⟨168490389634760036512929469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224653852846346715350572625 168490389634760036512929469)
    ·
      refine ⟨63183896113035013692348551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168490389634760036512929469 63183896113035013692348551)
      ·
        refine ⟨94775844169552520538522827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63183896113035013692348551 94775844169552520538522827)
        ·
          refine ⟨142163766254328780807784241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94775844169552520538522827 142163766254328780807784241)
          ·
            refine ⟨106622824690746585605838181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142163766254328780807784241 106622824690746585605838181)
            ·
              refine ⟨19991779629514984801094659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106622824690746585605838181 19991779629514984801094659)
              ·
                refine ⟨29987669444272477201641989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19991779629514984801094659 29987669444272477201641989)
                ·
                  refine ⟨5622688020801089475307873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29987669444272477201641989 5622688020801089475307873)
                  ·
                    refine ⟨4217016015600817106480905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5622688020801089475307873 4217016015600817106480905)
                    ·
                      refine ⟨3162762011700612829860679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4217016015600817106480905 3162762011700612829860679)
                      ·
                        rfl

theorem cell23_6159457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_6159457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159457 prefixEnd_6159457 := by exact prefixLift 6159457
  have htrace : WordTrace (prefixWord ++ tailWord_6159457) baseStart_6159457 baseEnd_6159457 := by
    simpa [prefixWord, tailWord_6159457, baseEnd_6159457] using wordTrace_append hprefix tailTrace_6159457
  have hstable : (prefixWord ++ tailWord_6159457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159457).length < 2 ^ (prefixWord ++ tailWord_6159457).sum := by decide
  have hdescent : baseEnd_6159457 < baseStart_6159457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159474 : List Nat := [3, 2, 1, 2, 2, 1, 3, 3, 2, 2, 2]
def baseStart_6159474 : Nat := 118140960795 + 6159474 * 2 ^ 59
def prefixEnd_6159474 : Nat := 4983230072969 + 3 ^ 40 * 6159474 * 2
def baseEnd_6159474 : Nat := 3162770740871739263348101

theorem tailTrace_6159474 : CollatzResearch.WordTrace tailWord_6159474 prefixEnd_6159474 3162770740871739263348101 := by
  unfold tailWord_6159474
  simp only [CollatzResearch.WordTrace]
  refine ⟨56163618221821281813485369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149769648591523418169294317 56163618221821281813485369)
  ·
    refine ⟨42122713666365961360114027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56163618221821281813485369 42122713666365961360114027)
    ·
      refine ⟨63184070499548942040171041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42122713666365961360114027 63184070499548942040171041)
      ·
        refine ⟨47388052874661706530128281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63184070499548942040171041 47388052874661706530128281)
        ·
          refine ⟨35541039655996279897596211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47388052874661706530128281 35541039655996279897596211)
          ·
            refine ⟨53311559483994419846394317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35541039655996279897596211 53311559483994419846394317)
            ·
              refine ⟨19991834806497907442397869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53311559483994419846394317 19991834806497907442397869)
              ·
                refine ⟨7496938052436715290899201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19991834806497907442397869 7496938052436715290899201)
                ·
                  refine ⟨5622703539327536468174401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7496938052436715290899201 5622703539327536468174401)
                  ·
                    refine ⟨4217027654495652351130801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5622703539327536468174401 4217027654495652351130801)
                    ·
                      refine ⟨3162770740871739263348101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4217027654495652351130801 3162770740871739263348101)
                      ·
                        rfl

theorem cell23_6159474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_6159474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159474 prefixEnd_6159474 := by exact prefixLift 6159474
  have htrace : WordTrace (prefixWord ++ tailWord_6159474) baseStart_6159474 baseEnd_6159474 := by
    simpa [prefixWord, tailWord_6159474, baseEnd_6159474] using wordTrace_append hprefix tailTrace_6159474
  have hstable : (prefixWord ++ tailWord_6159474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159474).length < 2 ^ (prefixWord ++ tailWord_6159474).sum := by decide
  have hdescent : baseEnd_6159474 < baseStart_6159474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159500 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 4, 5, 2]
def baseStart_6159500 : Nat := 118140960795 + 6159500 * 2 ^ 59
def prefixEnd_6159500 : Nat := 4983230072969 + 3 ^ 40 * 6159500 * 2
def baseEnd_6159500 : Nat := 3162784091368756161622981

theorem tailTrace_6159500 : CollatzResearch.WordTrace tailWord_6159500 prefixEnd_6159500 3162784091368756161622981 := by
  unfold tailWord_6159500
  simp only [CollatzResearch.WordTrace]
  refine ⟨112327710592595466847193977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149770280790127289129591969 112327710592595466847193977)
  ·
    refine ⟨84245782944446600135395483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112327710592595466847193977 84245782944446600135395483)
    ·
      refine ⟨126368674416669900203093225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84245782944446600135395483 126368674416669900203093225)
      ·
        refine ⟨94776505812502425152319919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126368674416669900203093225 94776505812502425152319919)
        ·
          refine ⟨142164758718753637728479879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94776505812502425152319919 142164758718753637728479879)
          ·
            refine ⟨213247138078130456592719819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142164758718753637728479879 213247138078130456592719819)
            ·
              refine ⟨319870707117195684889079729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213247138078130456592719819 319870707117195684889079729)
              ·
                refine ⟨239903030337896763666809797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319870707117195684889079729 239903030337896763666809797)
                ·
                  refine ⟨44981818188355643187526837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 239903030337896763666809797 44981818188355643187526837)
                  ·
                    refine ⟨4217045455158341548830641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44981818188355643187526837 4217045455158341548830641)
                    ·
                      refine ⟨3162784091368756161622981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4217045455158341548830641 3162784091368756161622981)
                      ·
                        rfl

theorem cell23_6159500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_6159500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159500 prefixEnd_6159500 := by exact prefixLift 6159500
  have htrace : WordTrace (prefixWord ++ tailWord_6159500) baseStart_6159500 baseEnd_6159500 := by
    simpa [prefixWord, tailWord_6159500, baseEnd_6159500] using wordTrace_append hprefix tailTrace_6159500
  have hstable : (prefixWord ++ tailWord_6159500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159500).length < 2 ^ (prefixWord ++ tailWord_6159500).sum := by decide
  have hdescent : baseEnd_6159500 < baseStart_6159500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159513 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 5, 3, 4]
def baseStart_6159513 : Nat := 118140960795 + 6159513 * 2 ^ 59
def prefixEnd_6159513 : Nat := 4983230072969 + 3 ^ 40 * 6159513 * 2
def baseEnd_6159513 : Nat := 3162790766617264610760421

theorem tailTrace_6159513 : CollatzResearch.WordTrace tailWord_6159513 prefixEnd_6159513 3162790766617264610760421 := by
  unfold tailWord_6159513
  simp only [CollatzResearch.WordTrace]
  refine ⟨224655895334143836914611193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149770596889429224609740795 224655895334143836914611193)
  ·
    refine ⟨168491921500607877685958395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224655895334143836914611193 168491921500607877685958395)
    ·
      refine ⟨252737882250911816528937593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168491921500607877685958395 252737882250911816528937593)
      ·
        refine ⟨189553411688183862396703195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252737882250911816528937593 189553411688183862396703195)
        ·
          refine ⟨284330117532275793595054793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189553411688183862396703195 284330117532275793595054793)
          ·
            refine ⟨213247588149206845196291095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284330117532275793595054793 213247588149206845196291095)
            ·
              refine ⟨319871382223810267794436643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213247588149206845196291095 319871382223810267794436643)
              ·
                refine ⟨479807073335715401691654965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319871382223810267794436643 479807073335715401691654965)
                ·
                  refine ⟨44981913125223318908592653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 479807073335715401691654965 44981913125223318908592653)
                  ·
                    refine ⟨16868217421958744590722245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44981913125223318908592653 16868217421958744590722245)
                    ·
                      refine ⟨3162790766617264610760421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16868217421958744590722245 3162790766617264610760421)
                      ·
                        rfl

theorem cell23_6159513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_6159513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159513 prefixEnd_6159513 := by exact prefixLift 6159513
  have htrace : WordTrace (prefixWord ++ tailWord_6159513) baseStart_6159513 baseEnd_6159513 := by
    simpa [prefixWord, tailWord_6159513, baseEnd_6159513] using wordTrace_append hprefix tailTrace_6159513
  have hstable : (prefixWord ++ tailWord_6159513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159513).length < 2 ^ (prefixWord ++ tailWord_6159513).sum := by decide
  have hdescent : baseEnd_6159513 < baseStart_6159513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159514 : List Nat := [3, 1, 1, 5, 1, 1, 4, 2, 5]
def baseStart_6159514 : Nat := 118140960795 + 6159514 * 2 ^ 59
def prefixEnd_6159514 : Nat := 4983230072969 + 3 ^ 40 * 6159514 * 2
def baseEnd_6159514 : Nat := 351421253344213234094213

theorem tailTrace_6159514 : CollatzResearch.WordTrace tailWord_6159514 prefixEnd_6159514 351421253344213234094213 := by
  unfold tailWord_6159514
  simp only [CollatzResearch.WordTrace]
  refine ⟨56163982951785053521349399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149770621204760142723598397 56163982951785053521349399)
  ·
    refine ⟨84245974427677580282024099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56163982951785053521349399 84245974427677580282024099)
    ·
      refine ⟨126368961641516370423036149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84245974427677580282024099 126368961641516370423036149)
      ·
        refine ⟨11847090153892159727159639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126368961641516370423036149 11847090153892159727159639)
        ·
          refine ⟨17770635230838239590739459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11847090153892159727159639 17770635230838239590739459)
          ·
            refine ⟨26655952846257359386109189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17770635230838239590739459 26655952846257359386109189)
            ·
              refine ⟨4997991158673254884895473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26655952846257359386109189 4997991158673254884895473)
              ·
                refine ⟨3748493369004941163671605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4997991158673254884895473 3748493369004941163671605)
                ·
                  refine ⟨351421253344213234094213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3748493369004941163671605 351421253344213234094213)
                  ·
                    rfl

theorem cell23_6159514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 5].length) (baseStart_6159514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159514 prefixEnd_6159514 := by exact prefixLift 6159514
  have htrace : WordTrace (prefixWord ++ tailWord_6159514) baseStart_6159514 baseEnd_6159514 := by
    simpa [prefixWord, tailWord_6159514, baseEnd_6159514] using wordTrace_append hprefix tailTrace_6159514
  have hstable : (prefixWord ++ tailWord_6159514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159514).length < 2 ^ (prefixWord ++ tailWord_6159514).sum := by decide
  have hdescent : baseEnd_6159514 < baseStart_6159514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159570 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 8]
def baseStart_6159570 : Nat := 118140960795 + 6159570 * 2 ^ 59
def prefixEnd_6159570 : Nat := 4983230072969 + 3 ^ 40 * 6159570 * 2
def baseEnd_6159570 : Nat := 351424448334952320860851

theorem tailTrace_6159570 : CollatzResearch.WordTrace tailWord_6159570 prefixEnd_6159570 351424448334952320860851 := by
  unfold tailWord_6159570
  simp only [CollatzResearch.WordTrace]
  refine ⟨56164493573734333912359041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149771982863291557099624109 56164493573734333912359041)
  ·
    refine ⟨42123370180300750434269281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56164493573734333912359041 42123370180300750434269281)
    ·
      refine ⟨31592527635225562825701961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42123370180300750434269281 31592527635225562825701961)
      ·
        refine ⟨23694395726419172119276471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31592527635225562825701961 23694395726419172119276471)
        ·
          refine ⟨35541593589628758178914707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23694395726419172119276471 35541593589628758178914707)
          ·
            refine ⟨53312390384443137268372061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35541593589628758178914707 53312390384443137268372061)
            ·
              refine ⟨19992146394166176475639523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53312390384443137268372061 19992146394166176475639523)
              ·
                refine ⟨29988219591249264713459285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19992146394166176475639523 29988219591249264713459285)
                ·
                  refine ⟨351424448334952320860851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29988219591249264713459285 351424448334952320860851)
                  ·
                    rfl

theorem cell23_6159570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_6159570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159570 prefixEnd_6159570 := by exact prefixLift 6159570
  have htrace : WordTrace (prefixWord ++ tailWord_6159570) baseStart_6159570 baseEnd_6159570 := by
    simpa [prefixWord, tailWord_6159570, baseEnd_6159570] using wordTrace_append hprefix tailTrace_6159570
  have hstable : (prefixWord ++ tailWord_6159570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159570).length < 2 ^ (prefixWord ++ tailWord_6159570).sum := by decide
  have hdescent : baseEnd_6159570 < baseStart_6159570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159617 : List Nat := [1, 2, 4, 1, 1, 3, 2, 3, 1, 5]
def baseStart_6159617 : Nat := 118140960795 + 6159617 * 2 ^ 59
def prefixEnd_6159617 : Nat := 4983230072969 + 3 ^ 40 * 6159617 * 2
def baseEnd_6159617 : Nat := 1054281389535110734619981

theorem tailTrace_6159617 : CollatzResearch.WordTrace tailWord_6159617 prefixEnd_6159617 1054281389535110734619981 := by
  unfold tailWord_6159617
  simp only [CollatzResearch.WordTrace]
  refine ⟨224659688525767062676397105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149773125683844708450931403 224659688525767062676397105)
  ·
    refine ⟨168494766394325297007297829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224659688525767062676397105 168494766394325297007297829)
    ·
      refine ⟨31592768698935993188868343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168494766394325297007297829 31592768698935993188868343)
      ·
        refine ⟨47389153048403989783302515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31592768698935993188868343 47389153048403989783302515)
        ·
          refine ⟨71083729572605984674953773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47389153048403989783302515 71083729572605984674953773)
          ·
            refine ⟨26656398589727244253107665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71083729572605984674953773 26656398589727244253107665)
            ·
              refine ⟨19992298942295433189830749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26656398589727244253107665 19992298942295433189830749)
              ·
                refine ⟨7497112103360787446186531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19992298942295433189830749 7497112103360787446186531)
                ·
                  refine ⟨11245668155041181169279797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7497112103360787446186531 11245668155041181169279797)
                  ·
                    refine ⟨1054281389535110734619981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11245668155041181169279797 1054281389535110734619981)
                    ·
                      rfl

theorem cell23_6159617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_6159617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159617 prefixEnd_6159617 := by exact prefixLift 6159617
  have htrace : WordTrace (prefixWord ++ tailWord_6159617) baseStart_6159617 baseEnd_6159617 := by
    simpa [prefixWord, tailWord_6159617, baseEnd_6159617] using wordTrace_append hprefix tailTrace_6159617
  have hstable : (prefixWord ++ tailWord_6159617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159617).length < 2 ^ (prefixWord ++ tailWord_6159617).sum := by decide
  have hdescent : baseEnd_6159617 < baseStart_6159617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159667 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 4]
def baseStart_6159667 : Nat := 118140960795 + 6159667 * 2 ^ 59
def prefixEnd_6159667 : Nat := 4983230072969 + 3 ^ 40 * 6159667 * 2
def baseEnd_6159667 : Nat := 3162869842638057008234713

theorem tailTrace_6159667 : CollatzResearch.WordTrace tailWord_6159667 prefixEnd_6159667 3162869842638057008234713 := by
  unfold tailWord_6159667
  simp only [CollatzResearch.WordTrace]
  refine ⟨224661512175585921215717255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149774341450390614143811503 224661512175585921215717255)
  ·
    refine ⟨336992268263378881823575883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224661512175585921215717255 336992268263378881823575883)
    ·
      refine ⟨505488402395068322735363825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336992268263378881823575883 505488402395068322735363825)
      ·
        refine ⟨379116301796301242051522869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505488402395068322735363825 379116301796301242051522869)
        ·
          refine ⟨35542153293403241442330269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 379116301796301242051522869 35542153293403241442330269)
          ·
            refine ⟨13328307485026215540873851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35542153293403241442330269 13328307485026215540873851)
            ·
              refine ⟨19992461227539323311310777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13328307485026215540873851 19992461227539323311310777)
              ·
                refine ⟨14994345920654492483483083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19992461227539323311310777 14994345920654492483483083)
                ·
                  refine ⟨22491518880981738725224625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14994345920654492483483083 22491518880981738725224625)
                  ·
                    refine ⟨16868639160736304043918469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22491518880981738725224625 16868639160736304043918469)
                    ·
                      refine ⟨3162869842638057008234713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16868639160736304043918469 3162869842638057008234713)
                      ·
                        rfl

theorem cell23_6159667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_6159667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159667 prefixEnd_6159667 := by exact prefixLift 6159667
  have htrace : WordTrace (prefixWord ++ tailWord_6159667) baseStart_6159667 baseEnd_6159667 := by
    simpa [prefixWord, tailWord_6159667, baseEnd_6159667] using wordTrace_append hprefix tailTrace_6159667
  have hstable : (prefixWord ++ tailWord_6159667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159667).length < 2 ^ (prefixWord ++ tailWord_6159667).sum := by decide
  have hdescent : baseEnd_6159667 < baseStart_6159667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159677 : List Nat := [1, 4, 1, 5, 1, 11]
def baseStart_6159677 : Nat := 118140960795 + 6159677 * 2 ^ 59
def prefixEnd_6159677 : Nat := 4983230072969 + 3 ^ 40 * 6159677 * 2
def baseEnd_6159677 : Nat := 13015946409237045140369

theorem tailTrace_6159677 : CollatzResearch.WordTrace tailWord_6159677 prefixEnd_6159677 13015946409237045140369 := by
  unfold tailWord_6159677
  simp only [CollatzResearch.WordTrace]
  refine ⟨224661876905549692923581285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149774584603699795282387523 224661876905549692923581285)
  ·
    refine ⟨42124101919790567423171491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224661876905549692923581285 42124101919790567423171491)
    ·
      refine ⟨63186152879685851134757237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42124101919790567423171491 63186152879685851134757237)
      ·
        refine ⟨5923701832470548543883491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63186152879685851134757237 5923701832470548543883491)
        ·
          refine ⟨8885552748705822815825237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5923701832470548543883491 8885552748705822815825237)
          ·
            refine ⟨13015946409237045140369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8885552748705822815825237 13015946409237045140369)
            ·
              rfl

theorem cell23_6159677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 11].length) (baseStart_6159677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159677 prefixEnd_6159677 := by exact prefixLift 6159677
  have htrace : WordTrace (prefixWord ++ tailWord_6159677) baseStart_6159677 baseEnd_6159677 := by
    simpa [prefixWord, tailWord_6159677, baseEnd_6159677] using wordTrace_append hprefix tailTrace_6159677
  have hstable : (prefixWord ++ tailWord_6159677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159677).length < 2 ^ (prefixWord ++ tailWord_6159677).sum := by decide
  have hdescent : baseEnd_6159677 < baseStart_6159677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159681 : List Nat := [1, 2, 5, 2, 1, 2, 2, 2, 2, 4]
def baseStart_6159681 : Nat := 118140960795 + 6159681 * 2 ^ 59
def prefixEnd_6159681 : Nat := 4983230072969 + 3 ^ 40 * 6159681 * 2
def baseEnd_6159681 : Nat := 1054292343789073317819883

theorem tailTrace_6159681 : CollatzResearch.WordTrace tailWord_6159681 prefixEnd_6159681 1054292343789073317819883 := by
  unfold tailWord_6159681
  simp only [CollatzResearch.WordTrace]
  refine ⟨224662022797535201606726897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149774681865023467737817931 224662022797535201606726897)
  ·
    refine ⟨168496517098151401205045173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224662022797535201606726897 168496517098151401205045173)
    ·
      refine ⟨15796548477951693862972985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168496517098151401205045173 15796548477951693862972985)
      ·
        refine ⟨11847411358463770397229739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15796548477951693862972985 11847411358463770397229739)
        ·
          refine ⟨17771117037695655595844609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11847411358463770397229739 17771117037695655595844609)
          ·
            refine ⟨13328337778271741696883457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17771117037695655595844609 13328337778271741696883457)
            ·
              refine ⟨9996253333703806272662593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13328337778271741696883457 9996253333703806272662593)
              ·
                refine ⟨7497190000277854704496945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9996253333703806272662593 7497190000277854704496945)
                ·
                  refine ⟨5622892500208391028372709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7497190000277854704496945 5622892500208391028372709)
                  ·
                    refine ⟨1054292343789073317819883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5622892500208391028372709 1054292343789073317819883)
                    ·
                      rfl

theorem cell23_6159681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_6159681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159681 prefixEnd_6159681 := by exact prefixLift 6159681
  have htrace : WordTrace (prefixWord ++ tailWord_6159681) baseStart_6159681 baseEnd_6159681 := by
    simpa [prefixWord, tailWord_6159681, baseEnd_6159681] using wordTrace_append hprefix tailTrace_6159681
  have hstable : (prefixWord ++ tailWord_6159681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159681).length < 2 ^ (prefixWord ++ tailWord_6159681).sum := by decide
  have hdescent : baseEnd_6159681 < baseStart_6159681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159704 : List Nat := [2, 1, 2, 2, 1, 1, 3, 5, 2, 1, 3]
def baseStart_6159704 : Nat := 118140960795 + 6159704 * 2 ^ 59
def prefixEnd_6159704 : Nat := 4983230072969 + 3 ^ 40 * 6159704 * 2
def baseEnd_6159704 : Nat := 3162888841422273363472043

theorem tailTrace_6159704 : CollatzResearch.WordTrace tailWord_6159704 prefixEnd_6159704 3162888841422273363472043 := by
  unfold tailWord_6159704
  simp only [CollatzResearch.WordTrace]
  refine ⟨112331430838225938267407083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149775241117634584356542777 112331430838225938267407083)
  ·
    refine ⟨168497146257338907401110625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112331430838225938267407083 168497146257338907401110625)
    ·
      refine ⟨126372859693004180550832969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168497146257338907401110625 126372859693004180550832969)
      ·
        refine ⟨94779644769753135413124727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126372859693004180550832969 94779644769753135413124727)
        ·
          refine ⟨142169467154629703119687091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94779644769753135413124727 142169467154629703119687091)
          ·
            refine ⟨213254200731944554679530637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142169467154629703119687091 213254200731944554679530637)
            ·
              refine ⟨79970325274479208004823989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213254200731944554679530637 79970325274479208004823989)
              ·
                refine ⟨7497217994482425750452249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79970325274479208004823989 7497217994482425750452249)
                ·
                  refine ⟨5622913495861819312839187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7497217994482425750452249 5622913495861819312839187)
                  ·
                    refine ⟨8434370243792728969258781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5622913495861819312839187 8434370243792728969258781)
                    ·
                      refine ⟨3162888841422273363472043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8434370243792728969258781 3162888841422273363472043)
                      ·
                        rfl

theorem cell23_6159704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_6159704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159704 prefixEnd_6159704 := by exact prefixLift 6159704
  have htrace : WordTrace (prefixWord ++ tailWord_6159704) baseStart_6159704 baseEnd_6159704 := by
    simpa [prefixWord, tailWord_6159704, baseEnd_6159704] using wordTrace_append hprefix tailTrace_6159704
  have hstable : (prefixWord ++ tailWord_6159704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159704).length < 2 ^ (prefixWord ++ tailWord_6159704).sum := by decide
  have hdescent : baseEnd_6159704 < baseStart_6159704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159801 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 7]
def baseStart_6159801 : Nat := 118140960795 + 6159801 * 2 ^ 59
def prefixEnd_6159801 : Nat := 4983230072969 + 3 ^ 40 * 6159801 * 2
def baseEnd_6159801 : Nat := 351437627671751053773233

theorem tailTrace_6159801 : CollatzResearch.WordTrace tailWord_6159801 prefixEnd_6159801 351437627671751053773233 := by
  unfold tailWord_6159801
  simp only [CollatzResearch.WordTrace]
  refine ⟨224666399557100462101095257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149777599704733641400730171 224666399557100462101095257)
  ·
    refine ⟨168499799667825346575821443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224666399557100462101095257 168499799667825346575821443)
    ·
      refine ⟨252749699501738019863732165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168499799667825346575821443 252749699501738019863732165)
      ·
        refine ⟨47390568656575878724449781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252749699501738019863732165 47390568656575878724449781)
        ·
          refine ⟨4442865811553988630417167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47390568656575878724449781 4442865811553988630417167)
          ·
            refine ⟨6664298717330982945625751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4442865811553988630417167 6664298717330982945625751)
            ·
              refine ⟨9996448075996474418438627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6664298717330982945625751 9996448075996474418438627)
              ·
                refine ⟨14994672113994711627657941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9996448075996474418438627 14994672113994711627657941)
                ·
                  refine ⟨351437627671751053773233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14994672113994711627657941 351437627671751053773233)
                  ·
                    rfl

theorem cell23_6159801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 7].length) (baseStart_6159801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159801 prefixEnd_6159801 := by exact prefixLift 6159801
  have htrace : WordTrace (prefixWord ++ tailWord_6159801) baseStart_6159801 baseEnd_6159801 := by
    simpa [prefixWord, tailWord_6159801, baseEnd_6159801] using wordTrace_append hprefix tailTrace_6159801
  have hstable : (prefixWord ++ tailWord_6159801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159801).length < 2 ^ (prefixWord ++ tailWord_6159801).sum := by decide
  have hdescent : baseEnd_6159801 < baseStart_6159801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159812 : List Nat := [2, 3, 3, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_6159812 : Nat := 118140960795 + 6159812 * 2 ^ 59
def prefixEnd_6159812 : Nat := 4983230072969 + 3 ^ 40 * 6159812 * 2
def baseEnd_6159812 : Nat := 3162944297332958940921547

theorem tailTrace_6159812 : CollatzResearch.WordTrace tailWord_6159812 prefixEnd_6159812 3162944297332958940921547 := by
  unfold tailWord_6159812
  simp only [CollatzResearch.WordTrace]
  refine ⟨112333400380030305489872845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149777867173373740653163793 112333400380030305489872845)
  ·
    refine ⟨42125025142511364558702317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112333400380030305489872845 42125025142511364558702317)
    ·
      refine ⟨15796884428441761709513369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42125025142511364558702317 15796884428441761709513369)
      ·
        refine ⟨11847663321331321282135027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15796884428441761709513369 11847663321331321282135027)
        ·
          refine ⟨17771494981996981923202541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11847663321331321282135027 17771494981996981923202541)
          ·
            refine ⟨6664310618248868221200953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17771494981996981923202541 6664310618248868221200953)
            ·
              refine ⟨4998232963686651165900715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6664310618248868221200953 4998232963686651165900715)
              ·
                refine ⟨7497349445529976748851073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4998232963686651165900715 7497349445529976748851073)
                ·
                  refine ⟨5623012084147482561638305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7497349445529976748851073 5623012084147482561638305)
                  ·
                    refine ⟨4217259063110611921228729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5623012084147482561638305 4217259063110611921228729)
                    ·
                      refine ⟨3162944297332958940921547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4217259063110611921228729 3162944297332958940921547)
                      ·
                        rfl

theorem cell23_6159812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_6159812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159812 prefixEnd_6159812 := by exact prefixLift 6159812
  have htrace : WordTrace (prefixWord ++ tailWord_6159812) baseStart_6159812 baseEnd_6159812 := by
    simpa [prefixWord, tailWord_6159812, baseEnd_6159812] using wordTrace_append hprefix tailTrace_6159812
  have hstable : (prefixWord ++ tailWord_6159812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159812).length < 2 ^ (prefixWord ++ tailWord_6159812).sum := by decide
  have hdescent : baseEnd_6159812 < baseStart_6159812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159817 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 6, 1, 4]
def baseStart_6159817 : Nat := 118140960795 + 6159817 * 2 ^ 59
def prefixEnd_6159817 : Nat := 4983230072969 + 3 ^ 40 * 6159817 * 2
def baseEnd_6159817 : Nat := 3162946864736231421359023

theorem tailTrace_6159817 : CollatzResearch.WordTrace tailWord_6159817 prefixEnd_6159817 3162946864736231421359023 := by
  unfold tailWord_6159817
  simp only [CollatzResearch.WordTrace]
  refine ⟨224666983125042496833677705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149777988750028331222451803 224666983125042496833677705)
  ·
    refine ⟨168500237343781872625258279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224666983125042496833677705 168500237343781872625258279)
    ·
      refine ⟨252750356015672808937887419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168500237343781872625258279 252750356015672808937887419)
      ·
        refine ⟨379125534023509213406831129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252750356015672808937887419 379125534023509213406831129)
        ·
          refine ⟨284344150517631910055123347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379125534023509213406831129 284344150517631910055123347)
          ·
            refine ⟨426516225776447865082685021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284344150517631910055123347 426516225776447865082685021)
            ·
              refine ⟨159943584666167949406006883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426516225776447865082685021 159943584666167949406006883)
              ·
                refine ⟨239915376999251924109010325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159943584666167949406006883 239915376999251924109010325)
                ·
                  refine ⟨11246033296839933942609859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 239915376999251924109010325 11246033296839933942609859)
                  ·
                    refine ⟨16869049945259900913914789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11246033296839933942609859 16869049945259900913914789)
                    ·
                      refine ⟨3162946864736231421359023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16869049945259900913914789 3162946864736231421359023)
                      ·
                        rfl

theorem cell23_6159817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_6159817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159817 prefixEnd_6159817 := by exact prefixLift 6159817
  have htrace : WordTrace (prefixWord ++ tailWord_6159817) baseStart_6159817 baseEnd_6159817 := by
    simpa [prefixWord, tailWord_6159817, baseEnd_6159817] using wordTrace_append hprefix tailTrace_6159817
  have hstable : (prefixWord ++ tailWord_6159817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159817).length < 2 ^ (prefixWord ++ tailWord_6159817).sum := by decide
  have hdescent : baseEnd_6159817 < baseStart_6159817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159834 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_6159834 : Nat := 118140960795 + 6159834 * 2 ^ 59
def prefixEnd_6159834 : Nat := 4983230072969 + 3 ^ 40 * 6159834 * 2
def baseEnd_6159834 : Nat := 3162955593907357854846445

theorem tailTrace_6159834 : CollatzResearch.WordTrace tailWord_6159834 prefixEnd_6159834 3162955593907357854846445 := by
  unfold tailWord_6159834
  simp only [CollatzResearch.WordTrace]
  refine ⟨56166900791495227184261639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149778402110653939158031037 56166900791495227184261639)
  ·
    refine ⟨84250351187242840776392459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56166900791495227184261639 84250351187242840776392459)
    ·
      refine ⟨126375526780864261164588689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84250351187242840776392459 126375526780864261164588689)
      ·
        refine ⟨94781645085648195873441517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126375526780864261164588689 94781645085648195873441517)
        ·
          refine ⟨35543116907118073452540569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94781645085648195873441517 35543116907118073452540569)
          ·
            refine ⟨26657337680338555089405427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35543116907118073452540569 26657337680338555089405427)
            ·
              refine ⟨39986006520507832634108141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26657337680338555089405427 39986006520507832634108141)
              ·
                refine ⟨14994752445190437237790553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39986006520507832634108141 14994752445190437237790553)
                ·
                  refine ⟨11246064333892827928342915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14994752445190437237790553 11246064333892827928342915)
                  ·
                    refine ⟨16869096500839241892514373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11246064333892827928342915 16869096500839241892514373)
                    ·
                      refine ⟨3162955593907357854846445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16869096500839241892514373 3162955593907357854846445)
                      ·
                        rfl

theorem cell23_6159834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_6159834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159834 prefixEnd_6159834 := by exact prefixLift 6159834
  have htrace : WordTrace (prefixWord ++ tailWord_6159834) baseStart_6159834 baseEnd_6159834 := by
    simpa [prefixWord, tailWord_6159834, baseEnd_6159834] using wordTrace_append hprefix tailTrace_6159834
  have hstable : (prefixWord ++ tailWord_6159834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159834).length < 2 ^ (prefixWord ++ tailWord_6159834).sum := by decide
  have hdescent : baseEnd_6159834 < baseStart_6159834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159887 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 7, 5]
def baseStart_6159887 : Nat := 118140960795 + 6159887 * 2 ^ 59
def prefixEnd_6159887 : Nat := 4983230072969 + 3 ^ 40 * 6159887 * 2
def baseEnd_6159887 : Nat := 1054327602794015382494567

theorem tailTrace_6159887 : CollatzResearch.WordTrace tailWord_6159887 prefixEnd_6159887 1054327602794015382494567 := by
  unfold tailWord_6159887
  simp only [CollatzResearch.WordTrace]
  refine ⟨224669536234788898788725915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149779690823192599192483943 224669536234788898788725915)
  ·
    refine ⟨337004304352183348183088873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224669536234788898788725915 337004304352183348183088873)
    ·
      refine ⟨252753228264137511137316655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337004304352183348183088873 252753228264137511137316655)
      ·
        refine ⟨379129842396206266705974983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252753228264137511137316655 379129842396206266705974983)
        ·
          refine ⟨568694763594309400058962475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379129842396206266705974983 568694763594309400058962475)
          ·
            refine ⟨853042145391464100088443713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568694763594309400058962475 853042145391464100088443713)
            ·
              refine ⟨639781609043598075066332785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853042145391464100088443713 639781609043598075066332785)
              ·
                refine ⟨479836206782698556299749589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 639781609043598075066332785 479836206782698556299749589)
                ·
                  refine ⟨11246161096469497413275381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 479836206782698556299749589 11246161096469497413275381)
                  ·
                    refine ⟨1054327602794015382494567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11246161096469497413275381 1054327602794015382494567)
                    ·
                      rfl

theorem cell23_6159887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 5].length) (baseStart_6159887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159887 prefixEnd_6159887 := by exact prefixLift 6159887
  have htrace : WordTrace (prefixWord ++ tailWord_6159887) baseStart_6159887 baseEnd_6159887 := by
    simpa [prefixWord, tailWord_6159887, baseEnd_6159887] using wordTrace_append hprefix tailTrace_6159887
  have hstable : (prefixWord ++ tailWord_6159887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159887).length < 2 ^ (prefixWord ++ tailWord_6159887).sum := by decide
  have hdescent : baseEnd_6159887 < baseStart_6159887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159901 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_6159901 : Nat := 118140960795 + 6159901 * 2 ^ 59
def prefixEnd_6159901 : Nat := 4983230072969 + 3 ^ 40 * 6159901 * 2
def baseEnd_6159901 : Nat := 3162989997111209092708637

theorem tailTrace_6159901 : CollatzResearch.WordTrace tailWord_6159901 prefixEnd_6159901 3162989997111209092708637 := by
  unfold tailWord_6159901
  simp only [CollatzResearch.WordTrace]
  refine ⟨224670046856738179179735557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149780031237825452786490371 224670046856738179179735557)
  ·
    refine ⟨42125633785638408596200417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224670046856738179179735557 42125633785638408596200417)
    ·
      refine ⟨31594225339228806447150313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42125633785638408596200417 31594225339228806447150313)
      ·
        refine ⟨23695669004421604835362735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31594225339228806447150313 23695669004421604835362735)
        ·
          refine ⟨35543503506632407253044103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23695669004421604835362735 35543503506632407253044103)
          ·
            refine ⟨53315255259948610879566155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35543503506632407253044103 53315255259948610879566155)
            ·
              refine ⟨79972882889922916319349233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53315255259948610879566155 79972882889922916319349233)
              ·
                refine ⟨59979662167442187239511925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79972882889922916319349233 59979662167442187239511925)
                ·
                  refine ⟨5623093328197705053704243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59979662167442187239511925 5623093328197705053704243)
                  ·
                    refine ⟨8434639992296557580556365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5623093328197705053704243 8434639992296557580556365)
                    ·
                      refine ⟨3162989997111209092708637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8434639992296557580556365 3162989997111209092708637)
                      ·
                        rfl

theorem cell23_6159901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_6159901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159901 prefixEnd_6159901 := by exact prefixLift 6159901
  have htrace : WordTrace (prefixWord ++ tailWord_6159901) baseStart_6159901 baseEnd_6159901 := by
    simpa [prefixWord, tailWord_6159901, baseEnd_6159901] using wordTrace_append hprefix tailTrace_6159901
  have hstable : (prefixWord ++ tailWord_6159901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159901).length < 2 ^ (prefixWord ++ tailWord_6159901).sum := by decide
  have hdescent : baseEnd_6159901 < baseStart_6159901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159918 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_6159918 : Nat := 118140960795 + 6159918 * 2 ^ 59
def prefixEnd_6159918 : Nat := 4983230072969 + 3 ^ 40 * 6159918 * 2
def baseEnd_6159918 : Nat := 3162998726282335526196059

theorem tailTrace_6159918 : CollatzResearch.WordTrace tailWord_6159918 prefixEnd_6159918 3162998726282335526196059 := by
  unfold tailWord_6159918
  simp only [CollatzResearch.WordTrace]
  refine ⟨28083833362209573885388051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149780444598451060722069605 28083833362209573885388051)
  ·
    refine ⟨42125750043314360828082077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28083833362209573885388051 42125750043314360828082077)
    ·
      refine ⟨15797156266242885310530779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42125750043314360828082077 15797156266242885310530779)
      ·
        refine ⟨23695734399364327965796169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15797156266242885310530779 23695734399364327965796169)
        ·
          refine ⟨17771800799523245974347127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23695734399364327965796169 17771800799523245974347127)
          ·
            refine ⟨26657701199284868961520691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17771800799523245974347127 26657701199284868961520691)
            ·
              refine ⟨39986551798927303442281037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26657701199284868961520691 39986551798927303442281037)
              ·
                refine ⟨14994956924597738790855389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39986551798927303442281037 14994956924597738790855389)
                ·
                  refine ⟨5623108846724152046570771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14994956924597738790855389 5623108846724152046570771)
                  ·
                    refine ⟨8434663270086228069856157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5623108846724152046570771 8434663270086228069856157)
                    ·
                      refine ⟨3162998726282335526196059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8434663270086228069856157 3162998726282335526196059)
                      ·
                        rfl

theorem cell23_6159918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_6159918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159918 prefixEnd_6159918 := by exact prefixLift 6159918
  have htrace : WordTrace (prefixWord ++ tailWord_6159918) baseStart_6159918 baseEnd_6159918 := by
    simpa [prefixWord, tailWord_6159918, baseEnd_6159918] using wordTrace_append hprefix tailTrace_6159918
  have hstable : (prefixWord ++ tailWord_6159918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159918).length < 2 ^ (prefixWord ++ tailWord_6159918).sum := by decide
  have hdescent : baseEnd_6159918 < baseStart_6159918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159941 : List Nat := [1, 3, 1, 1, 1, 4, 4, 2, 1, 1, 4]
def baseStart_6159941 : Nat := 118140960795 + 6159941 * 2 ^ 59
def prefixEnd_6159941 : Nat := 4983230072969 + 3 ^ 40 * 6159941 * 2
def baseEnd_6159941 : Nat := 3163010536337388936208453

theorem tailTrace_6159941 : CollatzResearch.WordTrace tailWord_6159941 prefixEnd_6159941 3163010536337388936208453 := by
  unfold tailWord_6159941
  simp only [CollatzResearch.WordTrace]
  refine ⟨224671505776593266011191677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149781003851062177340794451 224671505776593266011191677)
  ·
    refine ⟨84251814666222474754196879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224671505776593266011191677 84251814666222474754196879)
    ·
      refine ⟨126377721999333712131295319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84251814666222474754196879 126377721999333712131295319)
      ·
        refine ⟨189566582999000568196942979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126377721999333712131295319 189566582999000568196942979)
        ·
          refine ⟨284349874498500852295414469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189566582999000568196942979 284349874498500852295414469)
          ·
            refine ⟨53315601468468909805390213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284349874498500852295414469 53315601468468909805390213)
            ·
              refine ⟨9996675275337920588510665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53315601468468909805390213 9996675275337920588510665)
              ·
                refine ⟨7497506456503440441382999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9996675275337920588510665 7497506456503440441382999)
                ·
                  refine ⟨11246259684755160662074499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7497506456503440441382999 11246259684755160662074499)
                  ·
                    refine ⟨16869389527132740993111749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11246259684755160662074499 16869389527132740993111749)
                    ·
                      refine ⟨3163010536337388936208453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16869389527132740993111749 3163010536337388936208453)
                      ·
                        rfl

theorem cell23_6159941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_6159941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159941 prefixEnd_6159941 := by exact prefixLift 6159941
  have htrace : WordTrace (prefixWord ++ tailWord_6159941) baseStart_6159941 baseEnd_6159941 := by
    simpa [prefixWord, tailWord_6159941, baseEnd_6159941] using wordTrace_append hprefix tailTrace_6159941
  have hstable : (prefixWord ++ tailWord_6159941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159941).length < 2 ^ (prefixWord ++ tailWord_6159941).sum := by decide
  have hdescent : baseEnd_6159941 < baseStart_6159941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159964 : List Nat := [2, 2, 4, 1, 2, 1, 11]
def baseStart_6159964 : Nat := 118140960795 + 6159964 * 2 ^ 59
def prefixEnd_6159964 : Nat := 4983230072969 + 3 ^ 40 * 6159964 * 2
def baseEnd_6159964 : Nat := 39049658597437559829887

theorem tailTrace_6159964 : CollatzResearch.WordTrace tailWord_6159964 prefixEnd_6159964 39049658597437559829887 := by
  unfold tailWord_6159964
  simp only [CollatzResearch.WordTrace]
  refine ⟨112336172327754970469639473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149781563103673293959519297 112336172327754970469639473)
  ·
    refine ⟨84252129245816227852229605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112336172327754970469639473 84252129245816227852229605)
    ·
      refine ⟨15797274233590542722293051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84252129245816227852229605 15797274233590542722293051)
      ·
        refine ⟨23695911350385814083439577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15797274233590542722293051 23695911350385814083439577)
        ·
          refine ⟨17771933512789360562579683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23695911350385814083439577 17771933512789360562579683)
          ·
            refine ⟨26657900269184040843869525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17771933512789360562579683 26657900269184040843869525)
            ·
              refine ⟨39049658597437559829887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26657900269184040843869525 39049658597437559829887)
              ·
                rfl

theorem cell23_6159964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 11].length) (baseStart_6159964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159964 prefixEnd_6159964 := by exact prefixLift 6159964
  have htrace : WordTrace (prefixWord ++ tailWord_6159964) baseStart_6159964 baseEnd_6159964 := by
    simpa [prefixWord, tailWord_6159964, baseEnd_6159964] using wordTrace_append hprefix tailTrace_6159964
  have hstable : (prefixWord ++ tailWord_6159964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159964).length < 2 ^ (prefixWord ++ tailWord_6159964).sum := by decide
  have hdescent : baseEnd_6159964 < baseStart_6159964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159975 : List Nat := [1, 1, 5, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_6159975 : Nat := 118140960795 + 6159975 * 2 ^ 59
def prefixEnd_6159975 : Nat := 4983230072969 + 3 ^ 40 * 6159975 * 2
def baseEnd_6159975 : Nat := 3163027994679641803183297

theorem tailTrace_6159975 : CollatzResearch.WordTrace tailWord_6159975 prefixEnd_6159975 3163027994679641803183297 := by
  unfold tailWord_6159975
  simp only [CollatzResearch.WordTrace]
  refine ⟨224672745858470089817929379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149781830572313393211952919 224672745858470089817929379)
  ·
    refine ⟨337009118787705134726894069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224672745858470089817929379 337009118787705134726894069)
    ·
      refine ⟨31594604886347356380646319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 337009118787705134726894069 31594604886347356380646319)
      ·
        refine ⟨47391907329521034570969479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31594604886347356380646319 47391907329521034570969479)
        ·
          refine ⟨71087860994281551856454219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47391907329521034570969479 71087860994281551856454219)
          ·
            refine ⟨106631791491422327784681329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71087860994281551856454219 106631791491422327784681329)
            ·
              refine ⟨79973843618566745838510997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106631791491422327784681329 79973843618566745838510997)
              ·
                refine ⟨3748773919620316211180203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79973843618566745838510997 3748773919620316211180203)
                ·
                  refine ⟨5623160879430474316770305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3748773919620316211180203 5623160879430474316770305)
                  ·
                    refine ⟨4217370659572855737577729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5623160879430474316770305 4217370659572855737577729)
                    ·
                      refine ⟨3163027994679641803183297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4217370659572855737577729 3163027994679641803183297)
                      ·
                        rfl

theorem cell23_6159975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_6159975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159975 prefixEnd_6159975 := by exact prefixLift 6159975
  have htrace : WordTrace (prefixWord ++ tailWord_6159975) baseStart_6159975 baseEnd_6159975 := by
    simpa [prefixWord, tailWord_6159975, baseEnd_6159975] using wordTrace_append hprefix tailTrace_6159975
  have hstable : (prefixWord ++ tailWord_6159975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159975).length < 2 ^ (prefixWord ++ tailWord_6159975).sum := by decide
  have hdescent : baseEnd_6159975 < baseStart_6159975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6159981 : List Nat := [1, 5, 1, 1, 4, 1, 2, 8]
def baseStart_6159981 : Nat := 118140960795 + 6159981 * 2 ^ 59
def prefixEnd_6159981 : Nat := 4983230072969 + 3 ^ 40 * 6159981 * 2
def baseEnd_6159981 : Nat := 117149299094946991841047

theorem tailTrace_6159981 : CollatzResearch.WordTrace tailWord_6159981 prefixEnd_6159981 117149299094946991841047 := by
  unfold tailWord_6159981
  simp only [CollatzResearch.WordTrace]
  refine ⟨224672964696448352842647797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149781976464298901895098531 224672964696448352842647797)
  ·
    refine ⟨21063090440292033078998231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224672964696448352842647797 21063090440292033078998231)
    ·
      refine ⟨31594635660438049618497347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21063090440292033078998231 31594635660438049618497347)
      ·
        refine ⟨47391953490657074427746021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31594635660438049618497347 47391953490657074427746021)
        ·
          refine ⟨8885991279498201455202379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47391953490657074427746021 8885991279498201455202379)
          ·
            refine ⟨13328986919247302182803569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8885991279498201455202379 13328986919247302182803569)
            ·
              refine ⟨9996740189435476637102677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13328986919247302182803569 9996740189435476637102677)
              ·
                refine ⟨117149299094946991841047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9996740189435476637102677 117149299094946991841047)
                ·
                  rfl

theorem cell23_6159981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 8].length) (baseStart_6159981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6159981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6159981 prefixEnd_6159981 := by exact prefixLift 6159981
  have htrace : WordTrace (prefixWord ++ tailWord_6159981) baseStart_6159981 baseEnd_6159981 := by
    simpa [prefixWord, tailWord_6159981, baseEnd_6159981] using wordTrace_append hprefix tailTrace_6159981
  have hstable : (prefixWord ++ tailWord_6159981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6159981).length < 2 ^ (prefixWord ++ tailWord_6159981).sum := by decide
  have hdescent : baseEnd_6159981 < baseStart_6159981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6159981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160081 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 2, 3, 3]
def baseStart_6160081 : Nat := 118140960795 + 6160081 * 2 ^ 59
def prefixEnd_6160081 : Nat := 4983230072969 + 3 ^ 40 * 6160081 * 2
def baseEnd_6160081 : Nat := 3163082423629018388457809

theorem tailTrace_6160081 : CollatzResearch.WordTrace tailWord_6160081 prefixEnd_6160081 3163082423629018388457809 := by
  unfold tailWord_6160081
  simp only [CollatzResearch.WordTrace]
  refine ⟨224676611996086069921288097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149784407997390713280858731 224676611996086069921288097)
  ·
    refine ⟨168507458997064552440966073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224676611996086069921288097 168507458997064552440966073)
    ·
      refine ⟨126380594247798414330724555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168507458997064552440966073 126380594247798414330724555)
      ·
        refine ⟨189570891371697621496086833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126380594247798414330724555 189570891371697621496086833)
        ·
          refine ⟨142178168528773216122065125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189570891371697621496086833 142178168528773216122065125)
          ·
            refine ⟨26658406599144978022887211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142178168528773216122065125 26658406599144978022887211)
            ·
              refine ⟨39987609898717467034330817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26658406599144978022887211 39987609898717467034330817)
              ·
                refine ⟨29990707424038100275748113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39987609898717467034330817 29990707424038100275748113)
                ·
                  refine ⟨22493030568028575206811085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29990707424038100275748113 22493030568028575206811085)
                  ·
                    refine ⟨8434886463010715702554157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22493030568028575206811085 8434886463010715702554157)
                    ·
                      refine ⟨3163082423629018388457809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8434886463010715702554157 3163082423629018388457809)
                      ·
                        rfl

theorem cell23_6160081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_6160081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160081 prefixEnd_6160081 := by exact prefixLift 6160081
  have htrace : WordTrace (prefixWord ++ tailWord_6160081) baseStart_6160081 baseEnd_6160081 := by
    simpa [prefixWord, tailWord_6160081, baseEnd_6160081] using wordTrace_append hprefix tailTrace_6160081
  have hstable : (prefixWord ++ tailWord_6160081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160081).length < 2 ^ (prefixWord ++ tailWord_6160081).sum := by decide
  have hdescent : baseEnd_6160081 < baseStart_6160081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160082 : List Nat := [3, 2, 2, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_6160082 : Nat := 118140960795 + 6160082 * 2 ^ 59
def prefixEnd_6160082 : Nat := 4983230072969 + 3 ^ 40 * 6160082 * 2
def baseEnd_6160082 : Nat := 3163082937109672884545305

theorem tailTrace_6160082 : CollatzResearch.WordTrace tailWord_6160082 prefixEnd_6160082 3163082937109672884545305 := by
  unfold tailWord_6160082
  simp only [CollatzResearch.WordTrace]
  refine ⟨56169162117270611773018625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149784432312721631394716333 56169162117270611773018625)
  ·
    refine ⟨42126871587952958829763969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56169162117270611773018625 42126871587952958829763969)
    ·
      refine ⟨31595153690964719122322977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42126871587952958829763969 31595153690964719122322977)
      ·
        refine ⟨23696365268223539341742233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31595153690964719122322977 23696365268223539341742233)
        ·
          refine ⟨17772273951167654506306675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23696365268223539341742233 17772273951167654506306675)
          ·
            refine ⟨26658410926751481759460013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17772273951167654506306675 26658410926751481759460013)
            ·
              refine ⟨9996904097531805659797505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26658410926751481759460013 9996904097531805659797505)
              ·
                refine ⟨7497678073148854244848129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9996904097531805659797505 7497678073148854244848129)
                ·
                  refine ⟨5623258554861640683636097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7497678073148854244848129 5623258554861640683636097)
                  ·
                    refine ⟨4217443916146230512727073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5623258554861640683636097 4217443916146230512727073)
                    ·
                      refine ⟨3163082937109672884545305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4217443916146230512727073 3163082937109672884545305)
                      ·
                        rfl

theorem cell23_6160082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_6160082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160082 prefixEnd_6160082 := by exact prefixLift 6160082
  have htrace : WordTrace (prefixWord ++ tailWord_6160082) baseStart_6160082 baseEnd_6160082 := by
    simpa [prefixWord, tailWord_6160082, baseEnd_6160082] using wordTrace_append hprefix tailTrace_6160082
  have hstable : (prefixWord ++ tailWord_6160082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160082).length < 2 ^ (prefixWord ++ tailWord_6160082).sum := by decide
  have hdescent : baseEnd_6160082 < baseStart_6160082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160099 : List Nat := [1, 1, 1, 7, 2, 1, 3, 1, 2, 2, 2]
def baseStart_6160099 : Nat := 118140960795 + 6160099 * 2 ^ 59
def prefixEnd_6160099 : Nat := 4983230072969 + 3 ^ 40 * 6160099 * 2
def baseEnd_6160099 : Nat := 3163091666280799318032727

theorem tailTrace_6160099 : CollatzResearch.WordTrace tailWord_6160099 prefixEnd_6160099 3163091666280799318032727 := by
  unfold tailWord_6160099
  simp only [CollatzResearch.WordTrace]
  refine ⟨224677268510020858995443351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149784845673347239330295567 224677268510020858995443351)
  ·
    refine ⟨337015902765031288493165027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224677268510020858995443351 337015902765031288493165027)
    ·
      refine ⟨505523854147546932739747541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337015902765031288493165027 505523854147546932739747541)
      ·
        refine ⟨11848215331583131236087833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 505523854147546932739747541 11848215331583131236087833)
        ·
          refine ⟨8886161498687348427065875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11848215331583131236087833 8886161498687348427065875)
          ·
            refine ⟨13329242248031022640598813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8886161498687348427065875 13329242248031022640598813)
            ·
              refine ⟨4998465843011633490224555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13329242248031022640598813 4998465843011633490224555)
              ·
                refine ⟨7497698764517450235336833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4998465843011633490224555 7497698764517450235336833)
                ·
                  refine ⟨5623274073388087676502625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7497698764517450235336833 5623274073388087676502625)
                  ·
                    refine ⟨4217455555041065757376969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5623274073388087676502625 4217455555041065757376969)
                    ·
                      refine ⟨3163091666280799318032727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4217455555041065757376969 3163091666280799318032727)
                      ·
                        rfl

theorem cell23_6160099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_6160099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160099 prefixEnd_6160099 := by exact prefixLift 6160099
  have htrace : WordTrace (prefixWord ++ tailWord_6160099) baseStart_6160099 baseEnd_6160099 := by
    simpa [prefixWord, tailWord_6160099, baseEnd_6160099] using wordTrace_append hprefix tailTrace_6160099
  have hstable : (prefixWord ++ tailWord_6160099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160099).length < 2 ^ (prefixWord ++ tailWord_6160099).sum := by decide
  have hdescent : baseEnd_6160099 < baseStart_6160099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160131 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 5, 4]
def baseStart_6160131 : Nat := 118140960795 + 6160131 * 2 ^ 59
def prefixEnd_6160131 : Nat := 4983230072969 + 3 ^ 40 * 6160131 * 2
def baseEnd_6160131 : Nat := 1054369365887247730944193

theorem tailTrace_6160131 : CollatzResearch.WordTrace tailWord_6160131 prefixEnd_6160131 1054369365887247730944193 := by
  unfold tailWord_6160131
  simp only [CollatzResearch.WordTrace]
  refine ⟨224678435645904928460608247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149785623763936618973738831 224678435645904928460608247)
  ·
    refine ⟨337017653468857392690912371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224678435645904928460608247 337017653468857392690912371)
    ·
      refine ⟨505526480203286089036368557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337017653468857392690912371 505526480203286089036368557)
      ·
        refine ⟨189572430076232283388638209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 505526480203286089036368557 189572430076232283388638209)
        ·
          refine ⟨142179322557174212541478657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189572430076232283388638209 142179322557174212541478657)
          ·
            refine ⟨106634491917880659406108993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142179322557174212541478657 106634491917880659406108993)
            ·
              refine ⟨79975868938410494554581745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106634491917880659406108993 79975868938410494554581745)
              ·
                refine ⟨59981901703807870915936309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79975868938410494554581745 59981901703807870915936309)
                ·
                  refine ⟨5623303284731987898369029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59981901703807870915936309 5623303284731987898369029)
                  ·
                    refine ⟨1054369365887247730944193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5623303284731987898369029 1054369365887247730944193)
                    ·
                      rfl

theorem cell23_6160131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 4].length) (baseStart_6160131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160131 prefixEnd_6160131 := by exact prefixLift 6160131
  have htrace : WordTrace (prefixWord ++ tailWord_6160131) baseStart_6160131 baseEnd_6160131 := by
    simpa [prefixWord, tailWord_6160131, baseEnd_6160131] using wordTrace_append hprefix tailTrace_6160131
  have hstable : (prefixWord ++ tailWord_6160131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160131).length < 2 ^ (prefixWord ++ tailWord_6160131).sum := by decide
  have hdescent : baseEnd_6160131 < baseStart_6160131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160138 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_6160138 : Nat := 118140960795 + 6160138 * 2 ^ 59
def prefixEnd_6160138 : Nat := 4983230072969 + 3 ^ 40 * 6160138 * 2
def baseEnd_6160138 : Nat := 3163111692026324665445047

theorem tailTrace_6160138 : CollatzResearch.WordTrace tailWord_6160138 prefixEnd_6160138 3163111692026324665445047 := by
  unfold tailWord_6160138
  simp only [CollatzResearch.WordTrace]
  refine ⟨56169672739219892164028267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149785793971253045770742045 56169672739219892164028267)
  ·
    refine ⟨84254509108829838246042401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56169672739219892164028267 84254509108829838246042401)
    ·
      refine ⟨63190881831622378684531801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84254509108829838246042401 63190881831622378684531801)
      ·
        refine ⟨47393161373716784013398851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63190881831622378684531801 47393161373716784013398851)
        ·
          refine ⟨71089742060575176020098277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47393161373716784013398851 71089742060575176020098277)
          ·
            refine ⟨13329326636357845503768427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71089742060575176020098277 13329326636357845503768427)
            ·
              refine ⟨19993989954536768255652641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13329326636357845503768427 19993989954536768255652641)
              ·
                refine ⟨14995492465902576191739481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19993989954536768255652641 14995492465902576191739481)
                ·
                  refine ⟨11246619349426932143804611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14995492465902576191739481 11246619349426932143804611)
                  ·
                    refine ⟨16869929024140398215706917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11246619349426932143804611 16869929024140398215706917)
                    ·
                      refine ⟨3163111692026324665445047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16869929024140398215706917 3163111692026324665445047)
                      ·
                        rfl

theorem cell23_6160138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_6160138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160138 prefixEnd_6160138 := by exact prefixLift 6160138
  have htrace : WordTrace (prefixWord ++ tailWord_6160138) baseStart_6160138 baseEnd_6160138 := by
    simpa [prefixWord, tailWord_6160138, baseEnd_6160138] using wordTrace_append hprefix tailTrace_6160138
  have hstable : (prefixWord ++ tailWord_6160138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160138).length < 2 ^ (prefixWord ++ tailWord_6160138).sum := by decide
  have hdescent : baseEnd_6160138 < baseStart_6160138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160245 : List Nat := [1, 3, 4, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_6160245 : Nat := 118140960795 + 6160245 * 2 ^ 59
def prefixEnd_6160245 : Nat := 4983230072969 + 3 ^ 40 * 6160245 * 2
def baseEnd_6160245 : Nat := 3163166634456355746807055

theorem tailTrace_6160245 : CollatzResearch.WordTrace tailWord_6160245 prefixEnd_6160245 3163166634456355746807055 := by
  unfold tailWord_6160245
  simp only [CollatzResearch.WordTrace]
  refine ⟨224682593567491925930258189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149788395711661283953505459 224682593567491925930258189)
  ·
    refine ⟨84255972587809472223846821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224682593567491925930258189 84255972587809472223846821)
    ·
      refine ⟨15797994860214276041971279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84255972587809472223846821 15797994860214276041971279)
      ·
        refine ⟨23696992290321414062956919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15797994860214276041971279 23696992290321414062956919)
        ·
          refine ⟨35545488435482121094435379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23696992290321414062956919 35545488435482121094435379)
          ·
            refine ⟨53318232653223181641653069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35545488435482121094435379 53318232653223181641653069)
            ·
              refine ⟨19994337244958693115619901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53318232653223181641653069 19994337244958693115619901)
              ·
                refine ⟨7497876466859509918357463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19994337244958693115619901 7497876466859509918357463)
                ·
                  refine ⟨11246814700289264877536195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7497876466859509918357463 11246814700289264877536195)
                  ·
                    refine ⟨16870222050433897316304293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11246814700289264877536195 16870222050433897316304293)
                    ·
                      refine ⟨3163166634456355746807055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16870222050433897316304293 3163166634456355746807055)
                      ·
                        rfl

theorem cell23_6160245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_6160245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160245 prefixEnd_6160245 := by exact prefixLift 6160245
  have htrace : WordTrace (prefixWord ++ tailWord_6160245) baseStart_6160245 baseEnd_6160245 := by
    simpa [prefixWord, tailWord_6160245, baseEnd_6160245] using wordTrace_append hprefix tailTrace_6160245
  have hstable : (prefixWord ++ tailWord_6160245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160245).length < 2 ^ (prefixWord ++ tailWord_6160245).sum := by decide
  have hdescent : baseEnd_6160245 < baseStart_6160245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160281 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 2, 7]
def baseStart_6160281 : Nat := 118140960795 + 6160281 * 2 ^ 59
def prefixEnd_6160281 : Nat := 4983230072969 + 3 ^ 40 * 6160281 * 2
def baseEnd_6160281 : Nat := 1054395039919972535318963

theorem tailTrace_6160281 : CollatzResearch.WordTrace tailWord_6160281 prefixEnd_6160281 1054395039919972535318963 := by
  unfold tailWord_6160281
  simp only [CollatzResearch.WordTrace]
  refine ⟨224683906595361504078568697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149789271063574336052379131 224683906595361504078568697)
  ·
    refine ⟨168512929946521128058926523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224683906595361504078568697 168512929946521128058926523)
    ·
      refine ⟨252769394919781692088389785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168512929946521128058926523 252769394919781692088389785)
      ·
        refine ⟨189577046189836269066292339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252769394919781692088389785 189577046189836269066292339)
        ·
          refine ⟨284365569284754403599438509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189577046189836269066292339 284365569284754403599438509)
          ·
            refine ⟨106637088481782901349789441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284365569284754403599438509 106637088481782901349789441)
            ·
              refine ⟨79977816361337176012342081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106637088481782901349789441 79977816361337176012342081)
              ·
                refine ⟨59983362271002882009256561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79977816361337176012342081 59983362271002882009256561)
                ·
                  refine ⟨44987521703252161506942421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59983362271002882009256561 44987521703252161506942421)
                  ·
                    refine ⟨1054395039919972535318963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44987521703252161506942421 1054395039919972535318963)
                    ·
                      rfl

theorem cell23_6160281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_6160281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160281 prefixEnd_6160281 := by exact prefixLift 6160281
  have htrace : WordTrace (prefixWord ++ tailWord_6160281) baseStart_6160281 baseEnd_6160281 := by
    simpa [prefixWord, tailWord_6160281, baseEnd_6160281] using wordTrace_append hprefix tailTrace_6160281
  have hstable : (prefixWord ++ tailWord_6160281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160281).length < 2 ^ (prefixWord ++ tailWord_6160281).sum := by decide
  have hdescent : baseEnd_6160281 < baseStart_6160281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160282 : List Nat := [3, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3]
def baseStart_6160282 : Nat := 118140960795 + 6160282 * 2 ^ 59
def prefixEnd_6160282 : Nat := 4983230072969 + 3 ^ 40 * 6160282 * 2
def baseEnd_6160282 : Nat := 3163185633240572102044385

theorem tailTrace_6160282 : CollatzResearch.WordTrace tailWord_6160282 prefixEnd_6160282 3163185633240572102044385 := by
  unfold tailWord_6160282
  simp only [CollatzResearch.WordTrace]
  refine ⟨56170985767089470312338775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149789295378905254166236733 56170985767089470312338775)
  ·
    refine ⟨84256478650634205468508163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56170985767089470312338775 84256478650634205468508163)
    ·
      refine ⟨126384717975951308202762245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84256478650634205468508163 126384717975951308202762245)
      ·
        refine ⟨23697134620490870288017921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126384717975951308202762245 23697134620490870288017921)
        ·
          refine ⟨17772850965368152716013441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23697134620490870288017921 17772850965368152716013441)
          ·
            refine ⟨13329638224026114537010081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17772850965368152716013441 13329638224026114537010081)
            ·
              refine ⟨9997228668019585902757561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13329638224026114537010081 9997228668019585902757561)
              ·
                refine ⟨7497921501014689427068171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9997228668019585902757561 7497921501014689427068171)
                ·
                  refine ⟨11246882251522034140602257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7497921501014689427068171 11246882251522034140602257)
                  ·
                    refine ⟨8435161688641525605451693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11246882251522034140602257 8435161688641525605451693)
                    ·
                      refine ⟨3163185633240572102044385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8435161688641525605451693 3163185633240572102044385)
                      ·
                        rfl

theorem cell23_6160282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_6160282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160282 prefixEnd_6160282 := by exact prefixLift 6160282
  have htrace : WordTrace (prefixWord ++ tailWord_6160282) baseStart_6160282 baseEnd_6160282 := by
    simpa [prefixWord, tailWord_6160282, baseEnd_6160282] using wordTrace_append hprefix tailTrace_6160282
  have hstable : (prefixWord ++ tailWord_6160282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160282).length < 2 ^ (prefixWord ++ tailWord_6160282).sum := by decide
  have hdescent : baseEnd_6160282 < baseStart_6160282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160285 : List Nat := [1, 4, 2, 1, 2, 4, 2, 7]
def baseStart_6160285 : Nat := 118140960795 + 6160285 * 2 ^ 59
def prefixEnd_6160285 : Nat := 4983230072969 + 3 ^ 40 * 6160285 * 2
def baseEnd_6160285 : Nat := 117155080506760577418773

theorem tailTrace_6160285 : CollatzResearch.WordTrace tailWord_6160285 prefixEnd_6160285 117155080506760577418773 := by
  unfold tailWord_6160285
  simp only [CollatzResearch.WordTrace]
  refine ⟨224684052487347012761714309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149789368324898008507809539 224684052487347012761714309)
  ·
    refine ⟨42128259841377564892821433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224684052487347012761714309 42128259841377564892821433)
    ·
      refine ⟨31596194881033173669616075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42128259841377564892821433 31596194881033173669616075)
      ·
        refine ⟨47394292321549760504424113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31596194881033173669616075 47394292321549760504424113)
        ·
          refine ⟨35545719241162320378318085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47394292321549760504424113 35545719241162320378318085)
          ·
            refine ⟨6664822357717935070934641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35545719241162320378318085 6664822357717935070934641)
            ·
              refine ⟨4998616768288451303200981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6664822357717935070934641 4998616768288451303200981)
              ·
                refine ⟨117155080506760577418773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4998616768288451303200981 117155080506760577418773)
                ·
                  rfl

theorem cell23_6160285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 7].length) (baseStart_6160285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160285 prefixEnd_6160285 := by exact prefixLift 6160285
  have htrace : WordTrace (prefixWord ++ tailWord_6160285) baseStart_6160285 baseEnd_6160285 := by
    simpa [prefixWord, tailWord_6160285, baseEnd_6160285] using wordTrace_append hprefix tailTrace_6160285
  have hstable : (prefixWord ++ tailWord_6160285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160285).length < 2 ^ (prefixWord ++ tailWord_6160285).sum := by decide
  have hdescent : baseEnd_6160285 < baseStart_6160285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160335 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 1, 4, 2]
def baseStart_6160335 : Nat := 118140960795 + 6160335 * 2 ^ 59
def prefixEnd_6160335 : Nat := 4983230072969 + 3 ^ 40 * 6160335 * 2
def baseEnd_6160335 : Nat := 3163212847715260394681641

theorem tailTrace_6160335 : CollatzResearch.WordTrace tailWord_6160335 prefixEnd_6160335 3163212847715260394681641 := by
  unfold tailWord_6160335
  simp only [CollatzResearch.WordTrace]
  refine ⟨224685876137165871301034459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149790584091443914200689639 224685876137165871301034459)
  ·
    refine ⟨337028814205748806951551689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224685876137165871301034459 337028814205748806951551689)
    ·
      refine ⟨252771610654311605213663767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337028814205748806951551689 252771610654311605213663767)
      ·
        refine ⟨379157415981467407820495651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252771610654311605213663767 379157415981467407820495651)
        ·
          refine ⟨568736123972201111730743477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379157415981467407820495651 568736123972201111730743477)
          ·
            refine ⟨53319011622393854224757201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 568736123972201111730743477 53319011622393854224757201)
            ·
              refine ⟨39989258716795390668567901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53319011622393854224757201 39989258716795390668567901)
              ·
                refine ⟨14995972018798271500712963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39989258716795390668567901 14995972018798271500712963)
                ·
                  refine ⟨22493958028197407251069445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14995972018798271500712963 22493958028197407251069445)
                  ·
                    refine ⟨4217617130287013859575521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22493958028197407251069445 4217617130287013859575521)
                    ·
                      refine ⟨3163212847715260394681641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4217617130287013859575521 3163212847715260394681641)
                      ·
                        rfl

theorem cell23_6160335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 4, 2].length) (baseStart_6160335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160335 prefixEnd_6160335 := by exact prefixLift 6160335
  have htrace : WordTrace (prefixWord ++ tailWord_6160335) baseStart_6160335 baseEnd_6160335 := by
    simpa [prefixWord, tailWord_6160335, baseEnd_6160335] using wordTrace_append hprefix tailTrace_6160335
  have hstable : (prefixWord ++ tailWord_6160335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160335).length < 2 ^ (prefixWord ++ tailWord_6160335).sum := by decide
  have hdescent : baseEnd_6160335 < baseStart_6160335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160382 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_6160382 : Nat := 118140960795 + 6160382 * 2 ^ 59
def prefixEnd_6160382 : Nat := 4983230072969 + 3 ^ 40 * 6160382 * 2
def baseEnd_6160382 : Nat := 3163236981306021710793925

theorem tailTrace_6160382 : CollatzResearch.WordTrace tailWord_6160382 prefixEnd_6160382 3163236981306021710793925 := by
  unfold tailWord_6160382
  simp only [CollatzResearch.WordTrace]
  refine ⟨28085948795999449790999425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149791726911997065551996933 28085948795999449790999425)
  ·
    refine ⟨21064461596999587343249569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28085948795999449790999425 21064461596999587343249569)
    ·
      refine ⟨15798346197749690507437177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21064461596999587343249569 15798346197749690507437177)
      ·
        refine ⟨11848759648312267880577883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15798346197749690507437177 11848759648312267880577883)
        ·
          refine ⟨17773139472468401820866825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11848759648312267880577883 17773139472468401820866825)
          ·
            refine ⟨13329854604351301365650119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17773139472468401820866825 13329854604351301365650119)
            ·
              refine ⟨19994781906526952048475179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13329854604351301365650119 19994781906526952048475179)
              ·
                refine ⟨29992172859790428072712769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19994781906526952048475179 29992172859790428072712769)
                ·
                  refine ⟨22494129644842821054534577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29992172859790428072712769 22494129644842821054534577)
                  ·
                    refine ⟨16870597233632115790900933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22494129644842821054534577 16870597233632115790900933)
                    ·
                      refine ⟨3163236981306021710793925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16870597233632115790900933 3163236981306021710793925)
                      ·
                        rfl

theorem cell23_6160382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_6160382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160382 prefixEnd_6160382 := by exact prefixLift 6160382
  have htrace : WordTrace (prefixWord ++ tailWord_6160382) baseStart_6160382 baseEnd_6160382 := by
    simpa [prefixWord, tailWord_6160382, baseEnd_6160382] using wordTrace_append hprefix tailTrace_6160382
  have hstable : (prefixWord ++ tailWord_6160382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160382).length < 2 ^ (prefixWord ++ tailWord_6160382).sum := by decide
  have hdescent : baseEnd_6160382 < baseStart_6160382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160385 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_6160385 : Nat := 118140960795 + 6160385 * 2 ^ 59
def prefixEnd_6160385 : Nat := 4983230072969 + 3 ^ 40 * 6160385 * 2
def baseEnd_6160385 : Nat := 3163238521747985199056411

theorem tailTrace_6160385 : CollatzResearch.WordTrace tailWord_6160385 prefixEnd_6160385 3163238521747985199056411 := by
  unfold tailWord_6160385
  simp only [CollatzResearch.WordTrace]
  refine ⟨224687699786984729840354609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149791799857989819893569739 224687699786984729840354609)
  ·
    refine ⟨168515774840238547380265957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224687699786984729840354609 168515774840238547380265957)
    ·
      refine ⟨31596707782544727633799867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168515774840238547380265957 31596707782544727633799867)
      ·
        refine ⟨47395061673817091450699801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31596707782544727633799867 47395061673817091450699801)
        ·
          refine ⟨35546296255362818588024851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47395061673817091450699801 35546296255362818588024851)
          ·
            refine ⟨53319444383044227882037277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35546296255362818588024851 53319444383044227882037277)
            ·
              refine ⟨19994791643641585455763979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53319444383044227882037277 19994791643641585455763979)
              ·
                refine ⟨29992187465462378183645969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19994791643641585455763979 29992187465462378183645969)
                ·
                  refine ⟨22494140599096783637734477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29992187465462378183645969 22494140599096783637734477)
                  ·
                    refine ⟨8435302724661293864150429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22494140599096783637734477 8435302724661293864150429)
                    ·
                      refine ⟨3163238521747985199056411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8435302724661293864150429 3163238521747985199056411)
                      ·
                        rfl

theorem cell23_6160385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_6160385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160385 prefixEnd_6160385 := by exact prefixLift 6160385
  have htrace : WordTrace (prefixWord ++ tailWord_6160385) baseStart_6160385 baseEnd_6160385 := by
    simpa [prefixWord, tailWord_6160385, baseEnd_6160385] using wordTrace_append hprefix tailTrace_6160385
  have hstable : (prefixWord ++ tailWord_6160385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160385).length < 2 ^ (prefixWord ++ tailWord_6160385).sum := by decide
  have hdescent : baseEnd_6160385 < baseStart_6160385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160395 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 2, 5, 2]
def baseStart_6160395 : Nat := 118140960795 + 6160395 * 2 ^ 59
def prefixEnd_6160395 : Nat := 4983230072969 + 3 ^ 40 * 6160395 * 2
def baseEnd_6160395 : Nat := 3163243656554530159931365

theorem tailTrace_6160395 : CollatzResearch.WordTrace tailWord_6160395 prefixEnd_6160395 3163243656554530159931365 := by
  unfold tailWord_6160395
  simp only [CollatzResearch.WordTrace]
  refine ⟨224688064516948501548218639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149792043011299001032145759 224688064516948501548218639)
  ·
    refine ⟨337032096775422752322327959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224688064516948501548218639 337032096775422752322327959)
    ·
      refine ⟨505548145163134128483491939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337032096775422752322327959 505548145163134128483491939)
      ·
        refine ⟨758322217744701192725237909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505548145163134128483491939 758322217744701192725237909)
        ·
          refine ⟨35546353956782868408995527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 758322217744701192725237909 35546353956782868408995527)
          ·
            refine ⟨53319530935174302613493291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35546353956782868408995527 53319530935174302613493291)
            ·
              refine ⟨79979296402761453920239937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53319530935174302613493291 79979296402761453920239937)
              ·
                refine ⟨59984472302071090440179953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79979296402761453920239937 59984472302071090440179953)
                ·
                  refine ⟨44988354226553317830134965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59984472302071090440179953 44988354226553317830134965)
                  ·
                    refine ⟨4217658208739373546575153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44988354226553317830134965 4217658208739373546575153)
                    ·
                      refine ⟨3163243656554530159931365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4217658208739373546575153 3163243656554530159931365)
                      ·
                        rfl

theorem cell23_6160395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 5, 2].length) (baseStart_6160395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160395 prefixEnd_6160395 := by exact prefixLift 6160395
  have htrace : WordTrace (prefixWord ++ tailWord_6160395) baseStart_6160395 baseEnd_6160395 := by
    simpa [prefixWord, tailWord_6160395, baseEnd_6160395] using wordTrace_append hprefix tailTrace_6160395
  have hstable : (prefixWord ++ tailWord_6160395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160395).length < 2 ^ (prefixWord ++ tailWord_6160395).sum := by decide
  have hdescent : baseEnd_6160395 < baseStart_6160395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160405 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 1, 7]
def baseStart_6160405 : Nat := 118140960795 + 6160405 * 2 ^ 59
def prefixEnd_6160405 : Nat := 4983230072969 + 3 ^ 40 * 6160405 * 2
def baseEnd_6160405 : Nat := 1054416263787025040268773

theorem tailTrace_6160405 : CollatzResearch.WordTrace tailWord_6160405 prefixEnd_6160405 1054416263787025040268773 := by
  unfold tailWord_6160405
  simp only [CollatzResearch.WordTrace]
  refine ⟨224688429246912273256082669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149792286164608182170721779 224688429246912273256082669)
  ·
    refine ⟨84258160967592102471031001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224688429246912273256082669 84258160967592102471031001)
    ·
      refine ⟨63193620725694076853273251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84258160967592102471031001 63193620725694076853273251)
      ·
        refine ⟨94790431088541115279909877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63193620725694076853273251 94790431088541115279909877)
        ·
          refine ⟨8886602914550729557491551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94790431088541115279909877 8886602914550729557491551)
          ·
            refine ⟨13329904371826094336237327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8886602914550729557491551 13329904371826094336237327)
            ·
              refine ⟨19994856557739141504355991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13329904371826094336237327 19994856557739141504355991)
              ·
                refine ⟨29992284836608712256533987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19994856557739141504355991 29992284836608712256533987)
                ·
                  refine ⟨44988427254913068384800981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29992284836608712256533987 44988427254913068384800981)
                  ·
                    refine ⟨1054416263787025040268773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44988427254913068384800981 1054416263787025040268773)
                    ·
                      rfl

theorem cell23_6160405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_6160405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160405 prefixEnd_6160405 := by exact prefixLift 6160405
  have htrace : WordTrace (prefixWord ++ tailWord_6160405) baseStart_6160405 baseEnd_6160405 := by
    simpa [prefixWord, tailWord_6160405, baseEnd_6160405] using wordTrace_append hprefix tailTrace_6160405
  have hstable : (prefixWord ++ tailWord_6160405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160405).length < 2 ^ (prefixWord ++ tailWord_6160405).sum := by decide
  have hdescent : baseEnd_6160405 < baseStart_6160405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160435 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 3, 4]
def baseStart_6160435 : Nat := 118140960795 + 6160435 * 2 ^ 59
def prefixEnd_6160435 : Nat := 4983230072969 + 3 ^ 40 * 6160435 * 2
def baseEnd_6160435 : Nat := 1054421398593570001143727

theorem tailTrace_6160435 : CollatzResearch.WordTrace tailWord_6160435 prefixEnd_6160435 1054421398593570001143727 := by
  unfold tailWord_6160435
  simp only [CollatzResearch.WordTrace]
  refine ⟨224689523436803588379674759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149793015624535725586449839 224689523436803588379674759)
  ·
    refine ⟨337034285155205382569512139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224689523436803588379674759 337034285155205382569512139)
    ·
      refine ⟨505551427732808073854268209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337034285155205382569512139 505551427732808073854268209)
      ·
        refine ⟨379163570799606055390701157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505551427732808073854268209 379163570799606055390701157)
        ·
          refine ⟨71093169524926135385756467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 379163570799606055390701157 71093169524926135385756467)
          ·
            refine ⟨106639754287389203078634701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71093169524926135385756467 106639754287389203078634701)
            ·
              refine ⟨39989907857770951154488013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106639754287389203078634701 39989907857770951154488013)
              ·
                refine ⟨14996215446664106682933005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39989907857770951154488013 14996215446664106682933005)
                ·
                  refine ⟨5623580792499040006099877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14996215446664106682933005 5623580792499040006099877)
                  ·
                    refine ⟨1054421398593570001143727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5623580792499040006099877 1054421398593570001143727)
                    ·
                      rfl

theorem cell23_6160435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 4].length) (baseStart_6160435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160435 prefixEnd_6160435 := by exact prefixLift 6160435
  have htrace : WordTrace (prefixWord ++ tailWord_6160435) baseStart_6160435 baseEnd_6160435 := by
    simpa [prefixWord, tailWord_6160435, baseEnd_6160435] using wordTrace_append hprefix tailTrace_6160435
  have hstable : (prefixWord ++ tailWord_6160435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160435).length < 2 ^ (prefixWord ++ tailWord_6160435).sum := by decide
  have hdescent : baseEnd_6160435 < baseStart_6160435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160445 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_6160445 : Nat := 118140960795 + 6160445 * 2 ^ 59
def prefixEnd_6160445 : Nat := 4983230072969 + 3 ^ 40 * 6160445 * 2
def baseEnd_6160445 : Nat := 3163269330587254964306135

theorem tailTrace_6160445 : CollatzResearch.WordTrace tailWord_6160445 prefixEnd_6160445 3163269330587254964306135 := by
  unfold tailWord_6160445
  simp only [CollatzResearch.WordTrace]
  refine ⟨224689888166767360087538789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149793258777844906725025859 224689888166767360087538789)
  ·
    refine ⟨42129354031268880016413523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224689888166767360087538789 42129354031268880016413523)
    ·
      refine ⟨63194031046903320024620285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42129354031268880016413523 63194031046903320024620285)
      ·
        refine ⟨23697761642588745009232607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63194031046903320024620285 23697761642588745009232607)
        ·
          refine ⟨35546642463883117513848911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23697761642588745009232607 35546642463883117513848911)
          ·
            refine ⟨53319963695824676270773367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35546642463883117513848911 53319963695824676270773367)
            ·
              refine ⟨79979945543737014406160051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53319963695824676270773367 79979945543737014406160051)
              ·
                refine ⟨119969918315605521609240077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79979945543737014406160051 119969918315605521609240077)
                ·
                  refine ⟨44988719368352070603465029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119969918315605521609240077 44988719368352070603465029)
                  ·
                    refine ⟨8435384881566013238149693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44988719368352070603465029 8435384881566013238149693)
                    ·
                      refine ⟨3163269330587254964306135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8435384881566013238149693 3163269330587254964306135)
                      ·
                        rfl

theorem cell23_6160445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_6160445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160445 prefixEnd_6160445 := by exact prefixLift 6160445
  have htrace : WordTrace (prefixWord ++ tailWord_6160445) baseStart_6160445 baseEnd_6160445 := by
    simpa [prefixWord, tailWord_6160445, baseEnd_6160445] using wordTrace_append hprefix tailTrace_6160445
  have hstable : (prefixWord ++ tailWord_6160445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160445).length < 2 ^ (prefixWord ++ tailWord_6160445).sum := by decide
  have hdescent : baseEnd_6160445 < baseStart_6160445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160469 : List Nat := [1, 3, 2, 2, 1, 3, 3, 3, 1, 4]
def baseStart_6160469 : Nat := 118140960795 + 6160469 * 2 ^ 59
def prefixEnd_6160469 : Nat := 4983230072969 + 3 ^ 40 * 6160469 * 2
def baseEnd_6160469 : Nat := 1054427218040987623468675

theorem tailTrace_6160469 : CollatzResearch.WordTrace tailWord_6160469 prefixEnd_6160469 1054427218040987623468675 := by
  unfold tailWord_6160469
  simp only [CollatzResearch.WordTrace]
  refine ⟨224690763518680412186412461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149793842345786941457608307 224690763518680412186412461)
  ·
    refine ⟨84259036319505154569904673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224690763518680412186412461 84259036319505154569904673)
    ·
      refine ⟨63194277239628865927428505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84259036319505154569904673 63194277239628865927428505)
      ·
        refine ⟨47395707929721649445571379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63194277239628865927428505 47395707929721649445571379)
        ·
          refine ⟨71093561894582474168357069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47395707929721649445571379 71093561894582474168357069)
          ·
            refine ⟨26660085710468427813133901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71093561894582474168357069 26660085710468427813133901)
            ·
              refine ⟨9997532141425660429925213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26660085710468427813133901 9997532141425660429925213)
              ·
                refine ⟨3749074553034622661221955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9997532141425660429925213 3749074553034622661221955)
                ·
                  refine ⟨5623611829551933991832933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3749074553034622661221955 5623611829551933991832933)
                  ·
                    refine ⟨1054427218040987623468675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5623611829551933991832933 1054427218040987623468675)
                    ·
                      rfl

theorem cell23_6160469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_6160469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160469 prefixEnd_6160469 := by exact prefixLift 6160469
  have htrace : WordTrace (prefixWord ++ tailWord_6160469) baseStart_6160469 baseEnd_6160469 := by
    simpa [prefixWord, tailWord_6160469, baseEnd_6160469] using wordTrace_append hprefix tailTrace_6160469
  have hstable : (prefixWord ++ tailWord_6160469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160469).length < 2 ^ (prefixWord ++ tailWord_6160469).sum := by decide
  have hdescent : baseEnd_6160469 < baseStart_6160469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160543 : List Nat := [1, 1, 2, 6, 1, 1, 4, 2, 1, 1, 3]
def baseStart_6160543 : Nat := 118140960795 + 6160543 * 2 ^ 59
def prefixEnd_6160543 : Nat := 4983230072969 + 3 ^ 40 * 6160543 * 2
def baseEnd_6160543 : Nat := 3163319651691395580880685

theorem tailTrace_6160543 : CollatzResearch.WordTrace tailWord_6160543 prefixEnd_6160543 3163319651691395580880685 := by
  unfold tailWord_6160543
  simp only [CollatzResearch.WordTrace]
  refine ⟨224693462520412322824606283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149795641680274881883070855 224693462520412322824606283)
  ·
    refine ⟨337040193780618484236909425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224693462520412322824606283 337040193780618484236909425)
    ·
      refine ⟨252780145335463863177682069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337040193780618484236909425 252780145335463863177682069)
      ·
        refine ⟨11849069312599868586453847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 252780145335463863177682069 11849069312599868586453847)
        ·
          refine ⟨17773603968899802879680771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11849069312599868586453847 17773603968899802879680771)
          ·
            refine ⟨26660405953349704319521157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17773603968899802879680771 26660405953349704319521157)
            ·
              refine ⟨4998826116253069559910217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26660405953349704319521157 4998826116253069559910217)
              ·
                refine ⟨3749119587189802169932663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4998826116253069559910217 3749119587189802169932663)
                ·
                  refine ⟨5623679380784703254898995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3749119587189802169932663 5623679380784703254898995)
                  ·
                    refine ⟨8435519071177054882348493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5623679380784703254898995 8435519071177054882348493)
                    ·
                      refine ⟨3163319651691395580880685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8435519071177054882348493 3163319651691395580880685)
                      ·
                        rfl

theorem cell23_6160543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_6160543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160543 prefixEnd_6160543 := by exact prefixLift 6160543
  have htrace : WordTrace (prefixWord ++ tailWord_6160543) baseStart_6160543 baseEnd_6160543 := by
    simpa [prefixWord, tailWord_6160543, baseEnd_6160543] using wordTrace_append hprefix tailTrace_6160543
  have hstable : (prefixWord ++ tailWord_6160543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160543).length < 2 ^ (prefixWord ++ tailWord_6160543).sum := by decide
  have hdescent : baseEnd_6160543 < baseStart_6160543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160549 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 3, 2, 2]
def baseStart_6160549 : Nat := 118140960795 + 6160549 * 2 ^ 59
def prefixEnd_6160549 : Nat := 4983230072969 + 3 ^ 40 * 6160549 * 2
def baseEnd_6160549 : Nat := 3163322732575322557405657

theorem tailTrace_6160549 : CollatzResearch.WordTrace tailWord_6160549 prefixEnd_6160549 3163322732575322557405657 := by
  unfold tailWord_6160549
  simp only [CollatzResearch.WordTrace]
  refine ⟨224693681358390585849324701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149795787572260390566216467 224693681358390585849324701)
  ·
    refine ⟨84260130509396469693496763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224693681358390585849324701 84260130509396469693496763)
    ·
      refine ⟨126390195764094704540245145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84260130509396469693496763 126390195764094704540245145)
      ·
        refine ⟨94792646823071028405183859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126390195764094704540245145 94792646823071028405183859)
        ·
          refine ⟨142188970234606542607775789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94792646823071028405183859 142188970234606542607775789)
          ·
            refine ⟨53320863837977453477915921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142188970234606542607775789 53320863837977453477915921)
            ·
              refine ⟨39990647878483090108436941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53320863837977453477915921 39990647878483090108436941)
              ·
                refine ⟨14996492954431158790663853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39990647878483090108436941 14996492954431158790663853)
                ·
                  refine ⟨5623684857911684546498945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14996492954431158790663853 5623684857911684546498945)
                  ·
                    refine ⟨4217763643433763409874209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5623684857911684546498945 4217763643433763409874209)
                    ·
                      refine ⟨3163322732575322557405657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4217763643433763409874209 3163322732575322557405657)
                      ·
                        rfl

theorem cell23_6160549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_6160549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160549 prefixEnd_6160549 := by exact prefixLift 6160549
  have htrace : WordTrace (prefixWord ++ tailWord_6160549) baseStart_6160549 baseEnd_6160549 := by
    simpa [prefixWord, tailWord_6160549, baseEnd_6160549] using wordTrace_append hprefix tailTrace_6160549
  have hstable : (prefixWord ++ tailWord_6160549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160549).length < 2 ^ (prefixWord ++ tailWord_6160549).sum := by decide
  have hdescent : baseEnd_6160549 < baseStart_6160549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160562 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_6160562 : Nat := 118140960795 + 6160562 * 2 ^ 59
def prefixEnd_6160562 : Nat := 4983230072969 + 3 ^ 40 * 6160562 * 2
def baseEnd_6160562 : Nat := 3163329407823831006543097

theorem tailTrace_6160562 : CollatzResearch.WordTrace tailWord_6160562 prefixEnd_6160562 3163329407823831006543097 := by
  unfold tailWord_6160562
  simp only [CollatzResearch.WordTrace]
  refine ⟨56173538876835872267386985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149796103671562326046365293 56173538876835872267386985)
  ·
    refine ⟨42130154157626904200540239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56173538876835872267386985 42130154157626904200540239)
    ·
      refine ⟨63195231236440356300810359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42130154157626904200540239 63195231236440356300810359)
      ·
        refine ⟨94792846854660534451215539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63195231236440356300810359 94792846854660534451215539)
        ·
          refine ⟨142189270281990801676823309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94792846854660534451215539 142189270281990801676823309)
          ·
            refine ⟨53320976355746550628808741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142189270281990801676823309 53320976355746550628808741)
            ·
              refine ⟨9997683066702478242901639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53320976355746550628808741 9997683066702478242901639)
              ·
                refine ⟨14996524600053717364352459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9997683066702478242901639 14996524600053717364352459)
                ·
                  refine ⟨22494786900080576046528689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14996524600053717364352459 22494786900080576046528689)
                  ·
                    refine ⟨16871090175060432034896517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22494786900080576046528689 16871090175060432034896517)
                    ·
                      refine ⟨3163329407823831006543097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16871090175060432034896517 3163329407823831006543097)
                      ·
                        rfl

theorem cell23_6160562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_6160562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160562 prefixEnd_6160562 := by exact prefixLift 6160562
  have htrace : WordTrace (prefixWord ++ tailWord_6160562) baseStart_6160562 baseEnd_6160562 := by
    simpa [prefixWord, tailWord_6160562, baseEnd_6160562] using wordTrace_append hprefix tailTrace_6160562
  have hstable : (prefixWord ++ tailWord_6160562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160562).length < 2 ^ (prefixWord ++ tailWord_6160562).sum := by decide
  have hdescent : baseEnd_6160562 < baseStart_6160562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160610 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6160610 : Nat := 118140960795 + 6160610 * 2 ^ 59
def prefixEnd_6160610 : Nat := 4983230072969 + 3 ^ 40 * 6160610 * 2
def baseEnd_6160610 : Nat := 1054451351631748939580959

theorem tailTrace_6160610 : CollatzResearch.WordTrace tailWord_6160610 prefixEnd_6160610 1054451351631748939580959 := by
  unfold tailWord_6160610
  simp only [CollatzResearch.WordTrace]
  refine ⟨56173976552792398316823821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149797270807446395511530189 56173976552792398316823821)
  ·
    refine ⟨21065241207297149368808933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56173976552792398316823821 21065241207297149368808933)
    ·
      refine ⟨3949732726368215506651675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21065241207297149368808933 3949732726368215506651675)
      ·
        refine ⟨5924599089552323259977513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3949732726368215506651675 5924599089552323259977513)
        ·
          refine ⟨4443449317164242444983135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5924599089552323259977513 4443449317164242444983135)
          ·
            refine ⟨6665173975746363667474703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4443449317164242444983135 6665173975746363667474703)
            ·
              refine ⟨9997760963619545501212055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6665173975746363667474703 9997760963619545501212055)
              ·
                refine ⟨14996641445429318251818083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9997760963619545501212055 14996641445429318251818083)
                ·
                  refine ⟨22494962168143977377727125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14996641445429318251818083 22494962168143977377727125)
                  ·
                    refine ⟨1054451351631748939580959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22494962168143977377727125 1054451351631748939580959)
                    ·
                      rfl

theorem cell23_6160610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6160610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160610 prefixEnd_6160610 := by exact prefixLift 6160610
  have htrace : WordTrace (prefixWord ++ tailWord_6160610) baseStart_6160610 baseEnd_6160610 := by
    simpa [prefixWord, tailWord_6160610, baseEnd_6160610] using wordTrace_append hprefix tailTrace_6160610
  have hstable : (prefixWord ++ tailWord_6160610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160610).length < 2 ^ (prefixWord ++ tailWord_6160610).sum := by decide
  have hdescent : baseEnd_6160610 < baseStart_6160610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160626 : List Nat := [3, 2, 1, 3, 2, 1, 1, 4, 1, 3, 2]
def baseStart_6160626 : Nat := 118140960795 + 6160626 * 2 ^ 59
def prefixEnd_6160626 : Nat := 4983230072969 + 3 ^ 40 * 6160626 * 2
def baseEnd_6160626 : Nat := 3163362270585718756142803

theorem tailTrace_6160626 : CollatzResearch.WordTrace tailWord_6160626 prefixEnd_6160626 3163362270585718756142803 := by
  unfold tailWord_6160626
  simp only [CollatzResearch.WordTrace]
  refine ⟨56174122444777906999969433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149797659852741085333251821 56174122444777906999969433)
  ·
    refine ⟨42130591833583430249977075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56174122444777906999969433 42130591833583430249977075)
    ·
      refine ⟨63195887750375145374965613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42130591833583430249977075 63195887750375145374965613)
      ·
        refine ⟨23698457906390679515612105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63195887750375145374965613 23698457906390679515612105)
        ·
          refine ⟨17773843429793009636709079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23698457906390679515612105 17773843429793009636709079)
          ·
            refine ⟨26660765144689514455063619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17773843429793009636709079 26660765144689514455063619)
            ·
              refine ⟨39991147717034271682595429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26660765144689514455063619 39991147717034271682595429)
              ·
                refine ⟨7498340196943925940486643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39991147717034271682595429 7498340196943925940486643)
                ·
                  refine ⟨11247510295415888910729965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7498340196943925940486643 11247510295415888910729965)
                  ·
                    refine ⟨4217816360780958341523737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11247510295415888910729965 4217816360780958341523737)
                    ·
                      refine ⟨3163362270585718756142803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4217816360780958341523737 3163362270585718756142803)
                      ·
                        rfl

theorem cell23_6160626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_6160626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160626 prefixEnd_6160626 := by exact prefixLift 6160626
  have htrace : WordTrace (prefixWord ++ tailWord_6160626) baseStart_6160626 baseEnd_6160626 := by
    simpa [prefixWord, tailWord_6160626, baseEnd_6160626] using wordTrace_append hprefix tailTrace_6160626
  have hstable : (prefixWord ++ tailWord_6160626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160626).length < 2 ^ (prefixWord ++ tailWord_6160626).sum := by decide
  have hdescent : baseEnd_6160626 < baseStart_6160626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160639 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 6, 2, 2]
def baseStart_6160639 : Nat := 118140960795 + 6160639 * 2 ^ 59
def prefixEnd_6160639 : Nat := 4983230072969 + 3 ^ 40 * 6160639 * 2
def baseEnd_6160639 : Nat := 3163368945834227205280243

theorem tailTrace_6160639 : CollatzResearch.WordTrace tailWord_6160639 prefixEnd_6160639 3163368945834227205280243 := by
  unfold tailWord_6160639
  simp only [CollatzResearch.WordTrace]
  refine ⟨224696963928064531220100971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149797975952043020813400647 224696963928064531220100971)
  ·
    refine ⟨337045445892096796830151457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224696963928064531220100971 337045445892096796830151457)
    ·
      refine ⟨252784084419072597622613593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337045445892096796830151457 252784084419072597622613593)
      ·
        refine ⟨189588063314304448216960195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252784084419072597622613593 189588063314304448216960195)
        ·
          refine ⟨284382094971456672325440293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189588063314304448216960195 284382094971456672325440293)
          ·
            refine ⟨53321642807148126061020055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284382094971456672325440293 53321642807148126061020055)
            ·
              refine ⟨79982464210722189091530083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53321642807148126061020055 79982464210722189091530083)
              ·
                refine ⟨119973696316083283637295125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79982464210722189091530083 119973696316083283637295125)
                ·
                  refine ⟨5623767014816403920498209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119973696316083283637295125 5623767014816403920498209)
                  ·
                    refine ⟨4217825261112302940373657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5623767014816403920498209 4217825261112302940373657)
                    ·
                      refine ⟨3163368945834227205280243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4217825261112302940373657 3163368945834227205280243)
                      ·
                        rfl

theorem cell23_6160639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 2, 2].length) (baseStart_6160639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160639 prefixEnd_6160639 := by exact prefixLift 6160639
  have htrace : WordTrace (prefixWord ++ tailWord_6160639) baseStart_6160639 baseEnd_6160639 := by
    simpa [prefixWord, tailWord_6160639, baseEnd_6160639] using wordTrace_append hprefix tailTrace_6160639
  have hstable : (prefixWord ++ tailWord_6160639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160639).length < 2 ^ (prefixWord ++ tailWord_6160639).sum := by decide
  have hdescent : baseEnd_6160639 < baseStart_6160639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160673 : List Nat := [1, 2, 3, 2, 1, 1, 6, 1, 2, 2, 2]
def baseStart_6160673 : Nat := 118140960795 + 6160673 * 2 ^ 59
def prefixEnd_6160673 : Nat := 4983230072969 + 3 ^ 40 * 6160673 * 2
def baseEnd_6160673 : Nat := 3163386404176480072255087

theorem tailTrace_6160673 : CollatzResearch.WordTrace tailWord_6160673 prefixEnd_6160673 3163386404176480072255087 := by
  unfold tailWord_6160673
  simp only [CollatzResearch.WordTrace]
  refine ⟨224698204009941355026838673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149798802673294236684559115 224698204009941355026838673)
  ·
    refine ⟨168523653007456016270129005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224698204009941355026838673 168523653007456016270129005)
    ·
      refine ⟨63196369877796006101298377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168523653007456016270129005 63196369877796006101298377)
      ·
        refine ⟨47397277408347004575973783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63196369877796006101298377 47397277408347004575973783)
        ·
          refine ⟨71095916112520506863960675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47397277408347004575973783 71095916112520506863960675)
          ·
            refine ⟨106643874168780760295941013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71095916112520506863960675 106643874168780760295941013)
            ·
              refine ⟨4998931601661598138872235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106643874168780760295941013 4998931601661598138872235)
              ·
                refine ⟨7498397402492397208308353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4998931601661598138872235 7498397402492397208308353)
                ·
                  refine ⟨5623798051869297906231265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7498397402492397208308353 5623798051869297906231265)
                  ·
                    refine ⟨4217848538901973429673449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5623798051869297906231265 4217848538901973429673449)
                    ·
                      refine ⟨3163386404176480072255087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4217848538901973429673449 3163386404176480072255087)
                      ·
                        rfl

theorem cell23_6160673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_6160673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160673 prefixEnd_6160673 := by exact prefixLift 6160673
  have htrace : WordTrace (prefixWord ++ tailWord_6160673) baseStart_6160673 baseEnd_6160673 := by
    simpa [prefixWord, tailWord_6160673, baseEnd_6160673] using wordTrace_append hprefix tailTrace_6160673
  have hstable : (prefixWord ++ tailWord_6160673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160673).length < 2 ^ (prefixWord ++ tailWord_6160673).sum := by decide
  have hdescent : baseEnd_6160673 < baseStart_6160673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160739 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 3, 4]
def baseStart_6160739 : Nat := 118140960795 + 6160739 * 2 ^ 59
def prefixEnd_6160739 : Nat := 4983230072969 + 3 ^ 40 * 6160739 * 2
def baseEnd_6160739 : Nat := 1054473431299892271343261

theorem tailTrace_6160739 : CollatzResearch.WordTrace tailWord_6160739 prefixEnd_6160739 1054473431299892271343261 := by
  unfold tailWord_6160739
  simp only [CollatzResearch.WordTrace]
  refine ⟨224700611227702248298741271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149800407485134832199160847 224700611227702248298741271)
  ·
    refine ⟨337050916841553372448111907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224700611227702248298741271 337050916841553372448111907)
    ·
      refine ⟨505576375262330058672167861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337050916841553372448111907 505576375262330058672167861)
      ·
        refine ⟨47397785180843443000515737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 505576375262330058672167861 47397785180843443000515737)
        ·
          refine ⟨35548338885632582250386803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47397785180843443000515737 35548338885632582250386803)
          ·
            refine ⟨53322508328448873375580205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35548338885632582250386803 53322508328448873375580205)
            ·
              refine ⟨19995940623168327515842577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53322508328448873375580205 19995940623168327515842577)
              ·
                refine ⟨14996955467376245636881933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19995940623168327515842577 14996955467376245636881933)
                ·
                  refine ⟨5623858300266092113830725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14996955467376245636881933 5623858300266092113830725)
                  ·
                    refine ⟨1054473431299892271343261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5623858300266092113830725 1054473431299892271343261)
                    ·
                      rfl

theorem cell23_6160739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 4].length) (baseStart_6160739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160739 prefixEnd_6160739 := by exact prefixLift 6160739
  have htrace : WordTrace (prefixWord ++ tailWord_6160739) baseStart_6160739 baseEnd_6160739 := by
    simpa [prefixWord, tailWord_6160739, baseEnd_6160739] using wordTrace_append hprefix tailTrace_6160739
  have hstable : (prefixWord ++ tailWord_6160739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160739).length < 2 ^ (prefixWord ++ tailWord_6160739).sum := by decide
  have hdescent : baseEnd_6160739 < baseStart_6160739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160746 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_6160746 : Nat := 118140960795 + 6160746 * 2 ^ 59
def prefixEnd_6160746 : Nat := 4983230072969 + 3 ^ 40 * 6160746 * 2
def baseEnd_6160746 : Nat := 3163423888264258286642251

theorem tailTrace_6160746 : CollatzResearch.WordTrace tailWord_6160746 prefixEnd_6160746 3163423888264258286642251 := by
  unfold tailWord_6160746
  simp only [CollatzResearch.WordTrace]
  refine ⟨56175216634669222123561523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149800577692451258996164061 56175216634669222123561523)
  ·
    refine ⟨84262824952003833185342285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56175216634669222123561523 84262824952003833185342285)
    ·
      refine ⟨31598559357001437444503357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84262824952003833185342285 31598559357001437444503357)
      ·
        refine ⟨11849459758875539041688759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31598559357001437444503357 11849459758875539041688759)
        ·
          refine ⟨17774189638313308562533139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11849459758875539041688759 17774189638313308562533139)
          ·
            refine ⟨26661284457469962843799709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17774189638313308562533139 26661284457469962843799709)
            ·
              refine ⟨9997981671551236066424891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26661284457469962843799709 9997981671551236066424891)
              ·
                refine ⟨14996972507326854099637337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9997981671551236066424891 14996972507326854099637337)
                ·
                  refine ⟨11247729380495140574728003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14996972507326854099637337 11247729380495140574728003)
                  ·
                    refine ⟨16871594070742710862092005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11247729380495140574728003 16871594070742710862092005)
                    ·
                      refine ⟨3163423888264258286642251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16871594070742710862092005 3163423888264258286642251)
                      ·
                        rfl

theorem cell23_6160746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_6160746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160746 prefixEnd_6160746 := by exact prefixLift 6160746
  have htrace : WordTrace (prefixWord ++ tailWord_6160746) baseStart_6160746 baseEnd_6160746 := by
    simpa [prefixWord, tailWord_6160746, baseEnd_6160746] using wordTrace_append hprefix tailTrace_6160746
  have hstable : (prefixWord ++ tailWord_6160746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160746).length < 2 ^ (prefixWord ++ tailWord_6160746).sum := by decide
  have hdescent : baseEnd_6160746 < baseStart_6160746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160749 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_6160749 : Nat := 118140960795 + 6160749 * 2 ^ 59
def prefixEnd_6160749 : Nat := 4983230072969 + 3 ^ 40 * 6160749 * 2
def baseEnd_6160749 : Nat := 3163425428706221774904737

theorem tailTrace_6160749 : CollatzResearch.WordTrace tailWord_6160749 prefixEnd_6160749 3163425428706221774904737 := by
  unfold tailWord_6160749
  simp only [CollatzResearch.WordTrace]
  refine ⟨224700975957666020006605301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149800650638444013337736867 224700975957666020006605301)
  ·
    refine ⟨21065716496031189375619247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224700975957666020006605301 21065716496031189375619247)
    ·
      refine ⟨31598574744046784063428871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21065716496031189375619247 31598574744046784063428871)
      ·
        refine ⟨47397862116070176095143307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31598574744046784063428871 47397862116070176095143307)
        ·
          refine ⟨71096793174105264142714961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47397862116070176095143307 71096793174105264142714961)
          ·
            refine ⟨53322594880578948107036221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71096793174105264142714961 53322594880578948107036221)
            ·
              refine ⟨19995973080217105540138583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53322594880578948107036221 19995973080217105540138583)
              ·
                refine ⟨29993959620325658310207875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19995973080217105540138583 29993959620325658310207875)
                ·
                  refine ⟨44990939430488487465311813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29993959620325658310207875 44990939430488487465311813)
                  ·
                    refine ⟨8435801143216591399745965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44990939430488487465311813 8435801143216591399745965)
                    ·
                      refine ⟨3163425428706221774904737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8435801143216591399745965 3163425428706221774904737)
                      ·
                        rfl

theorem cell23_6160749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_6160749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160749 prefixEnd_6160749 := by exact prefixLift 6160749
  have htrace : WordTrace (prefixWord ++ tailWord_6160749) baseStart_6160749 baseEnd_6160749 := by
    simpa [prefixWord, tailWord_6160749, baseEnd_6160749] using wordTrace_append hprefix tailTrace_6160749
  have hstable : (prefixWord ++ tailWord_6160749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160749).length < 2 ^ (prefixWord ++ tailWord_6160749).sum := by decide
  have hdescent : baseEnd_6160749 < baseStart_6160749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160769 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 8]
def baseStart_6160769 : Nat := 118140960795 + 6160769 * 2 ^ 59
def prefixEnd_6160769 : Nat := 4983230072969 + 3 ^ 40 * 6160769 * 2
def baseEnd_6160769 : Nat := 351492855368812410739405

theorem tailTrace_6160769 : CollatzResearch.WordTrace tailWord_6160769 prefixEnd_6160769 351492855368812410739405 := by
  unfold tailWord_6160769
  simp only [CollatzResearch.WordTrace]
  refine ⟨224701705417593563422333361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149801136945062375614888907 224701705417593563422333361)
  ·
    refine ⟨168526279063195172566750021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224701705417593563422333361 168526279063195172566750021)
    ·
      refine ⟨31598677324349094856265629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168526279063195172566750021 31598677324349094856265629)
      ·
        refine ⟨11849503996630910571099611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31598677324349094856265629 11849503996630910571099611)
        ·
          refine ⟨17774255994946365856649417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11849503996630910571099611 17774255994946365856649417)
          ·
            refine ⟨13330691996209774392487063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17774255994946365856649417 13330691996209774392487063)
            ·
              refine ⟨19996037994314661588730595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13330691996209774392487063 19996037994314661588730595)
              ·
                refine ⟨29994056991471992383095893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19996037994314661588730595 29994056991471992383095893)
                ·
                  refine ⟨351492855368812410739405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29994056991471992383095893 351492855368812410739405)
                  ·
                    rfl

theorem cell23_6160769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 8].length) (baseStart_6160769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160769 prefixEnd_6160769 := by exact prefixLift 6160769
  have htrace : WordTrace (prefixWord ++ tailWord_6160769) baseStart_6160769 baseEnd_6160769 := by
    simpa [prefixWord, tailWord_6160769, baseEnd_6160769] using wordTrace_append hprefix tailTrace_6160769
  have hstable : (prefixWord ++ tailWord_6160769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160769).length < 2 ^ (prefixWord ++ tailWord_6160769).sum := by decide
  have hdescent : baseEnd_6160769 < baseStart_6160769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160772 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_6160772 : Nat := 118140960795 + 6160772 * 2 ^ 59
def prefixEnd_6160772 : Nat := 4983230072969 + 3 ^ 40 * 6160772 * 2
def baseEnd_6160772 : Nat := 3163437238761275184917131

theorem tailTrace_6160772 : CollatzResearch.WordTrace tailWord_6160772 prefixEnd_6160772 3163437238761275184917131 := by
  unfold tailWord_6160772
  simp only [CollatzResearch.WordTrace]
  refine ⟨112350907418291347467346285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149801209891055129956461713 112350907418291347467346285)
  ·
    refine ⟨42131590281859255300254857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112350907418291347467346285 42131590281859255300254857)
    ·
      refine ⟨31598692711394441475191143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42131590281859255300254857 31598692711394441475191143)
      ·
        refine ⟨47398039067091662212786715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31598692711394441475191143 47398039067091662212786715)
        ·
          refine ⟨71097058600637493319180073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47398039067091662212786715 71097058600637493319180073)
          ·
            refine ⟨53322793950478119989385055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71097058600637493319180073 53322793950478119989385055)
            ·
              refine ⟨79984190925717179984077583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53322793950478119989385055 79984190925717179984077583)
              ·
                refine ⟨119976286388575769976116375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79984190925717179984077583 119976286388575769976116375)
                ·
                  refine ⟨179964429582863654964174563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119976286388575769976116375 179964429582863654964174563)
                  ·
                    refine ⟨269946644374295482446261845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 179964429582863654964174563 269946644374295482446261845)
                    ·
                      refine ⟨3163437238761275184917131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 269946644374295482446261845 3163437238761275184917131)
                      ·
                        rfl

theorem cell23_6160772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_6160772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160772 prefixEnd_6160772 := by exact prefixLift 6160772
  have htrace : WordTrace (prefixWord ++ tailWord_6160772) baseStart_6160772 baseEnd_6160772 := by
    simpa [prefixWord, tailWord_6160772, baseEnd_6160772] using wordTrace_append hprefix tailTrace_6160772
  have hstable : (prefixWord ++ tailWord_6160772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160772).length < 2 ^ (prefixWord ++ tailWord_6160772).sum := by decide
  have hdescent : baseEnd_6160772 < baseStart_6160772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160812 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 3, 6]
def baseStart_6160812 : Nat := 118140960795 + 6160812 * 2 ^ 59
def prefixEnd_6160812 : Nat := 4983230072969 + 3 ^ 40 * 6160812 * 2
def baseEnd_6160812 : Nat := 1054485925995818342805649

theorem tailTrace_6160812 : CollatzResearch.WordTrace tailWord_6160812 prefixEnd_6160812 1054485925995818342805649 := by
  unfold tailWord_6160812
  simp only [CollatzResearch.WordTrace]
  refine ⟨112351636878218890883074345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149802182504291854510765793 112351636878218890883074345)
  ·
    refine ⟨84263727658664168162305759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112351636878218890883074345 84263727658664168162305759)
    ·
      refine ⟨126395591487996252243458639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84263727658664168162305759 126395591487996252243458639)
      ·
        refine ⟨189593387231994378365187959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126395591487996252243458639 189593387231994378365187959)
        ·
          refine ⟨284390080847991567547781939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189593387231994378365187959 284390080847991567547781939)
          ·
            refine ⟨426585121271987351321672909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284390080847991567547781939 426585121271987351321672909)
            ·
              refine ⟨159969420476995256745627341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426585121271987351321672909 159969420476995256745627341)
              ·
                refine ⟨59988532678873221279610253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159969420476995256745627341 59988532678873221279610253)
                ·
                  refine ⟨22495699754577457979853845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59988532678873221279610253 22495699754577457979853845)
                  ·
                    refine ⟨1054485925995818342805649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22495699754577457979853845 1054485925995818342805649)
                    ·
                      rfl

theorem cell23_6160812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_6160812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160812 prefixEnd_6160812 := by exact prefixLift 6160812
  have htrace : WordTrace (prefixWord ++ tailWord_6160812) baseStart_6160812 baseEnd_6160812 := by
    simpa [prefixWord, tailWord_6160812, baseEnd_6160812] using wordTrace_append hprefix tailTrace_6160812
  have hstable : (prefixWord ++ tailWord_6160812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160812).length < 2 ^ (prefixWord ++ tailWord_6160812).sum := by decide
  have hdescent : baseEnd_6160812 < baseStart_6160812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160839 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_6160839 : Nat := 118140960795 + 6160839 * 2 ^ 59
def prefixEnd_6160839 : Nat := 4983230072969 + 3 ^ 40 * 6160839 * 2
def baseEnd_6160839 : Nat := 3163471641965126422779323

theorem tailTrace_6160839 : CollatzResearch.WordTrace tailWord_6160839 prefixEnd_6160839 3163471641965126422779323 := by
  unfold tailWord_6160839
  simp only [CollatzResearch.WordTrace]
  refine ⟨224704258527339965377381571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149802839018226643584921047 224704258527339965377381571)
  ·
    refine ⟨337056387791009948066072357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224704258527339965377381571 337056387791009948066072357)
    ·
      refine ⟨63198072710814365262388567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337056387791009948066072357 63198072710814365262388567)
      ·
        refine ⟨94797109066221547893582851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63198072710814365262388567 94797109066221547893582851)
        ·
          refine ⟨142195663599332321840374277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94797109066221547893582851 142195663599332321840374277)
          ·
            refine ⟨26661686924874810345070177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142195663599332321840374277 26661686924874810345070177)
            ·
              refine ⟨19996265193656107758802633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26661686924874810345070177 19996265193656107758802633)
              ·
                refine ⟨14997198895242080819101975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19996265193656107758802633 14997198895242080819101975)
                ·
                  refine ⟨22495798342863121228652963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14997198895242080819101975 22495798342863121228652963)
                  ·
                    refine ⟨33743697514294681842979445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22495798342863121228652963 33743697514294681842979445)
                    ·
                      refine ⟨3163471641965126422779323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33743697514294681842979445 3163471641965126422779323)
                      ·
                        rfl

theorem cell23_6160839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_6160839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160839 prefixEnd_6160839 := by exact prefixLift 6160839
  have htrace : WordTrace (prefixWord ++ tailWord_6160839) baseStart_6160839 baseEnd_6160839 := by
    simpa [prefixWord, tailWord_6160839, baseEnd_6160839] using wordTrace_append hprefix tailTrace_6160839
  have hstable : (prefixWord ++ tailWord_6160839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160839).length < 2 ^ (prefixWord ++ tailWord_6160839).sum := by decide
  have hdescent : baseEnd_6160839 < baseStart_6160839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160850 : List Nat := [3, 2, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_6160850 : Nat := 118140960795 + 6160850 * 2 ^ 59
def prefixEnd_6160850 : Nat := 4983230072969 + 3 ^ 40 * 6160850 * 2
def baseEnd_6160850 : Nat := 1054492430084108626580591

theorem tailTrace_6160850 : CollatzResearch.WordTrace tailWord_6160850 prefixEnd_6160850 1054492430084108626580591 := by
  unfold tailWord_6160850
  simp only [CollatzResearch.WordTrace]
  refine ⟨56176164932575028564008001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149803106486866742837354669 56176164932575028564008001)
  ·
    refine ⟨42132123699431271423006001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56176164932575028564008001 42132123699431271423006001)
    ·
      refine ⟨31599092774573453567254501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42132123699431271423006001 31599092774573453567254501)
      ·
        refine ⟨5924829895232522543860219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31599092774573453567254501 5924829895232522543860219)
        ·
          refine ⟨8887244842848783815790329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5924829895232522543860219 8887244842848783815790329)
          ·
            refine ⟨6665433632136587861842747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8887244842848783815790329 6665433632136587861842747)
            ·
              refine ⟨9998150448204881792764121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6665433632136587861842747 9998150448204881792764121)
              ·
                refine ⟨7498612836153661344573091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9998150448204881792764121 7498612836153661344573091)
                ·
                  refine ⟨11247919254230492016859637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7498612836153661344573091 11247919254230492016859637)
                  ·
                    refine ⟨1054492430084108626580591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11247919254230492016859637 1054492430084108626580591)
                    ·
                      rfl

theorem cell23_6160850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_6160850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160850 prefixEnd_6160850 := by exact prefixLift 6160850
  have htrace : WordTrace (prefixWord ++ tailWord_6160850) baseStart_6160850 baseEnd_6160850 := by
    simpa [prefixWord, tailWord_6160850, baseEnd_6160850] using wordTrace_append hprefix tailTrace_6160850
  have hstable : (prefixWord ++ tailWord_6160850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160850).length < 2 ^ (prefixWord ++ tailWord_6160850).sum := by decide
  have hdescent : baseEnd_6160850 < baseStart_6160850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160853 : List Nat := [1, 3, 2, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_6160853 : Nat := 118140960795 + 6160853 * 2 ^ 59
def prefixEnd_6160853 : Nat := 4983230072969 + 3 ^ 40 * 6160853 * 2
def baseEnd_6160853 : Nat := 3163478830694289368004259

theorem tailTrace_6160853 : CollatzResearch.WordTrace tailWord_6160853 prefixEnd_6160853 3163478830694289368004259 := by
  unfold tailWord_6160853
  simp only [CollatzResearch.WordTrace]
  refine ⟨224704769149289245768391213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149803179432859497178927475 224704769149289245768391213)
  ·
    refine ⟨84264288430983467163146705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224704769149289245768391213 84264288430983467163146705)
    ·
      refine ⟨63198216323237600372360029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84264288430983467163146705 63198216323237600372360029)
      ·
        refine ⟨23699331121214100139635011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63198216323237600372360029 23699331121214100139635011)
        ·
          refine ⟨35548996681821150209452517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23699331121214100139635011 35548996681821150209452517)
          ·
            refine ⟨6665436877841465664272347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35548996681821150209452517 6665436877841465664272347)
            ·
              refine ⟨9998155316762198496408521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6665436877841465664272347 9998155316762198496408521)
              ·
                refine ⟨7498616487571648872306391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9998155316762198496408521 7498616487571648872306391)
                ·
                  refine ⟨11247924731357473308459587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7498616487571648872306391 11247924731357473308459587)
                  ·
                    refine ⟨16871887097036209962689381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11247924731357473308459587 16871887097036209962689381)
                    ·
                      refine ⟨3163478830694289368004259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16871887097036209962689381 3163478830694289368004259)
                      ·
                        rfl

theorem cell23_6160853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_6160853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160853 prefixEnd_6160853 := by exact prefixLift 6160853
  have htrace : WordTrace (prefixWord ++ tailWord_6160853) baseStart_6160853 baseEnd_6160853 := by
    simpa [prefixWord, tailWord_6160853, baseEnd_6160853] using wordTrace_append hprefix tailTrace_6160853
  have hstable : (prefixWord ++ tailWord_6160853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160853).length < 2 ^ (prefixWord ++ tailWord_6160853).sum := by decide
  have hdescent : baseEnd_6160853 < baseStart_6160853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160886 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_6160886 : Nat := 118140960795 + 6160886 * 2 ^ 59
def prefixEnd_6160886 : Nat := 4983230072969 + 3 ^ 40 * 6160886 * 2
def baseEnd_6160886 : Nat := 3163495775555887738891607

theorem tailTrace_6160886 : CollatzResearch.WordTrace tailWord_6160886 prefixEnd_6160886 3163495775555887738891607 := by
  unfold tailWord_6160886
  simp only [CollatzResearch.WordTrace]
  refine ⟨14044123297385605775271407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149803981838779794936228341 14044123297385605775271407)
  ·
    refine ⟨21066184946078408662907111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14044123297385605775271407 21066184946078408662907111)
    ·
      refine ⟨31599277419117612994360667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21066184946078408662907111 31599277419117612994360667)
      ·
        refine ⟨47398916128676419491541001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31599277419117612994360667 47398916128676419491541001)
        ·
          refine ⟨35549187096507314618655751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47398916128676419491541001 35549187096507314618655751)
          ·
            refine ⟨53323780644760971927983627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35549187096507314618655751 53323780644760971927983627)
            ·
              refine ⟨79985670967141457891975441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53323780644760971927983627 79985670967141457891975441)
              ·
                refine ⟨59989253225356093418981581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79985670967141457891975441 59989253225356093418981581)
                ·
                  refine ⟨22495969959508535032118093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59989253225356093418981581 22495969959508535032118093)
                  ·
                    refine ⟨8435988734815700637044285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22495969959508535032118093 8435988734815700637044285)
                    ·
                      refine ⟨3163495775555887738891607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8435988734815700637044285 3163495775555887738891607)
                      ·
                        rfl

theorem cell23_6160886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_6160886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160886 prefixEnd_6160886 := by exact prefixLift 6160886
  have htrace : WordTrace (prefixWord ++ tailWord_6160886) baseStart_6160886 baseEnd_6160886 := by
    simpa [prefixWord, tailWord_6160886, baseEnd_6160886] using wordTrace_append hprefix tailTrace_6160886
  have hstable : (prefixWord ++ tailWord_6160886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160886).length < 2 ^ (prefixWord ++ tailWord_6160886).sum := by decide
  have hdescent : baseEnd_6160886 < baseStart_6160886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160903 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_6160903 : Nat := 118140960795 + 6160903 * 2 ^ 59
def prefixEnd_6160903 : Nat := 4983230072969 + 3 ^ 40 * 6160903 * 2
def baseEnd_6160903 : Nat := 3163504504727014172379029

theorem tailTrace_6160903 : CollatzResearch.WordTrace tailWord_6160903 prefixEnd_6160903 3163504504727014172379029 := by
  unfold tailWord_6160903
  simp only [CollatzResearch.WordTrace]
  refine ⟨224706592799108104307711363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149804395199405402871807575 224706592799108104307711363)
  ·
    refine ⟨337059889198662156461567045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224706592799108104307711363 337059889198662156461567045)
    ·
      refine ⟨63198729224749154336543821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337059889198662156461567045 63198729224749154336543821)
      ·
        refine ⟨23699523459280932876203933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63198729224749154336543821 23699523459280932876203933)
        ·
          refine ⟨8887321297230349828576475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23699523459280932876203933 8887321297230349828576475)
          ·
            refine ⟨13330981945845524742864713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8887321297230349828576475 13330981945845524742864713)
            ·
              refine ⟨9998236459384143557148535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13330981945845524742864713 9998236459384143557148535)
              ·
                refine ⟨14997354689076215335722803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9998236459384143557148535 14997354689076215335722803)
                ·
                  refine ⟨22496032033614323003584205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14997354689076215335722803 22496032033614323003584205)
                  ·
                    refine ⟨8436012012605371126344077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22496032033614323003584205 8436012012605371126344077)
                    ·
                      refine ⟨3163504504727014172379029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8436012012605371126344077 3163504504727014172379029)
                      ·
                        rfl

theorem cell23_6160903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_6160903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160903 prefixEnd_6160903 := by exact prefixLift 6160903
  have htrace : WordTrace (prefixWord ++ tailWord_6160903) baseStart_6160903 baseEnd_6160903 := by
    simpa [prefixWord, tailWord_6160903, baseEnd_6160903] using wordTrace_append hprefix tailTrace_6160903
  have hstable : (prefixWord ++ tailWord_6160903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160903).length < 2 ^ (prefixWord ++ tailWord_6160903).sum := by decide
  have hdescent : baseEnd_6160903 < baseStart_6160903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160929 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_6160929 : Nat := 118140960795 + 6160929 * 2 ^ 59
def prefixEnd_6160929 : Nat := 4983230072969 + 3 ^ 40 * 6160929 * 2
def baseEnd_6160929 : Nat := 3163517855224031070653909

theorem tailTrace_6160929 : CollatzResearch.WordTrace tailWord_6160929 prefixEnd_6160929 3163517855224031070653909 := by
  unfold tailWord_6160929
  simp only [CollatzResearch.WordTrace]
  refine ⟨224707541097013910748157841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149805027398009273832105227 224707541097013910748157841)
  ·
    refine ⟨168530655822760433061118381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224707541097013910748157841 168530655822760433061118381)
    ·
      refine ⟨63198995933535162397919393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168530655822760433061118381 63198995933535162397919393)
      ·
        refine ⟨47399246950151371798439545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63198995933535162397919393 47399246950151371798439545)
        ·
          refine ⟨35549435212613528848829659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47399246950151371798439545 35549435212613528848829659)
          ·
            refine ⟨53324152818920293273244489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35549435212613528848829659 53324152818920293273244489)
            ·
              refine ⟨39993114614190219954933367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53324152818920293273244489 39993114614190219954933367)
              ·
                refine ⟨59989671921285329932400051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39993114614190219954933367 59989671921285329932400051)
                ·
                  refine ⟨89984507881927994898600077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59989671921285329932400051 89984507881927994898600077)
                  ·
                    refine ⟨33744190455722998086975029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89984507881927994898600077 33744190455722998086975029)
                    ·
                      refine ⟨3163517855224031070653909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33744190455722998086975029 3163517855224031070653909)
                      ·
                        rfl

theorem cell23_6160929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_6160929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160929 prefixEnd_6160929 := by exact prefixLift 6160929
  have htrace : WordTrace (prefixWord ++ tailWord_6160929) baseStart_6160929 baseEnd_6160929 := by
    simpa [prefixWord, tailWord_6160929, baseEnd_6160929] using wordTrace_append hprefix tailTrace_6160929
  have hstable : (prefixWord ++ tailWord_6160929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160929).length < 2 ^ (prefixWord ++ tailWord_6160929).sum := by decide
  have hdescent : baseEnd_6160929 < baseStart_6160929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160936 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 2, 6]
def baseStart_6160936 : Nat := 118140960795 + 6160936 * 2 ^ 59
def prefixEnd_6160936 : Nat := 4983230072969 + 3 ^ 40 * 6160936 * 2
def baseEnd_6160936 : Nat := 1054507149862870847755459

theorem tailTrace_6160936 : CollatzResearch.WordTrace tailWord_6160936 prefixEnd_6160936 1054507149862870847755459 := by
  unfold tailWord_6160936
  simp only [CollatzResearch.WordTrace]
  refine ⟨112353898203994275471831331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149805197605325700629108441 112353898203994275471831331)
  ·
    refine ⟨168530847305991413207746997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112353898203994275471831331 168530847305991413207746997)
    ·
      refine ⟨15799766934936694988226281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168530847305991413207746997 15799766934936694988226281)
      ·
        refine ⟨11849825201202521241169711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15799766934936694988226281 11849825201202521241169711)
        ·
          refine ⟨17774737801803781861754567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11849825201202521241169711 17774737801803781861754567)
          ·
            refine ⟨26662106702705672792631851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17774737801803781861754567 26662106702705672792631851)
            ·
              refine ⟨39993160054058509188947777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26662106702705672792631851 39993160054058509188947777)
              ·
                refine ⟨29994870040543881891710833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39993160054058509188947777 29994870040543881891710833)
                ·
                  refine ⟨22496152530407911418783125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29994870040543881891710833 22496152530407911418783125)
                  ·
                    refine ⟨1054507149862870847755459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22496152530407911418783125 1054507149862870847755459)
                    ·
                      rfl

theorem cell23_6160936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_6160936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160936 prefixEnd_6160936 := by exact prefixLift 6160936
  have htrace : WordTrace (prefixWord ++ tailWord_6160936) baseStart_6160936 baseEnd_6160936 := by
    simpa [prefixWord, tailWord_6160936, baseEnd_6160936] using wordTrace_append hprefix tailTrace_6160936
  have hstable : (prefixWord ++ tailWord_6160936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160936).length < 2 ^ (prefixWord ++ tailWord_6160936).sum := by decide
  have hdescent : baseEnd_6160936 < baseStart_6160936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160956 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_6160956 : Nat := 118140960795 + 6160956 * 2 ^ 59
def prefixEnd_6160956 : Nat := 4983230072969 + 3 ^ 40 * 6160956 * 2
def baseEnd_6160956 : Nat := 3163531719201702465016285

theorem tailTrace_6160956 : CollatzResearch.WordTrace tailWord_6160956 prefixEnd_6160956 3163531719201702465016285 := by
  unfold tailWord_6160956
  simp only [CollatzResearch.WordTrace]
  refine ⟨112354262933958047179695361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149805683911944062906260481 112354262933958047179695361)
  ·
    refine ⟨84265697200468535384771521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112354262933958047179695361 84265697200468535384771521)
    ·
      refine ⟨63199272900351401538578641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84265697200468535384771521 63199272900351401538578641)
      ·
        refine ⟨47399454675263551153933981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63199272900351401538578641 47399454675263551153933981)
        ·
          refine ⟨17774795503223831682725243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47399454675263551153933981 17774795503223831682725243)
          ·
            refine ⟨26662193254835747524087865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17774795503223831682725243 26662193254835747524087865)
            ·
              refine ⟨19996644941126810643065899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26662193254835747524087865 19996644941126810643065899)
              ·
                refine ⟨29994967411690215964598849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19996644941126810643065899 29994967411690215964598849)
                ·
                  refine ⟨22496225558767661973449137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29994967411690215964598849 22496225558767661973449137)
                  ·
                    refine ⟨16872169169075746480086853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22496225558767661973449137 16872169169075746480086853)
                    ·
                      refine ⟨3163531719201702465016285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16872169169075746480086853 3163531719201702465016285)
                      ·
                        rfl

theorem cell23_6160956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_6160956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160956 prefixEnd_6160956 := by exact prefixLift 6160956
  have htrace : WordTrace (prefixWord ++ tailWord_6160956) baseStart_6160956 baseEnd_6160956 := by
    simpa [prefixWord, tailWord_6160956, baseEnd_6160956] using wordTrace_append hprefix tailTrace_6160956
  have hstable : (prefixWord ++ tailWord_6160956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160956).length < 2 ^ (prefixWord ++ tailWord_6160956).sum := by decide
  have hdescent : baseEnd_6160956 < baseStart_6160956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160986 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2]
def baseStart_6160986 : Nat := 118140960795 + 6160986 * 2 ^ 59
def prefixEnd_6160986 : Nat := 4983230072969 + 3 ^ 40 * 6160986 * 2
def baseEnd_6160986 : Nat := 3163547123621337347641147

theorem tailTrace_6160986 : CollatzResearch.WordTrace tailWord_6160986 prefixEnd_6160986 3163547123621337347641147 := by
  unfold tailWord_6160986
  simp only [CollatzResearch.WordTrace]
  refine ⟨56177405014451852370745703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149806413371871606321988541 56177405014451852370745703)
  ·
    refine ⟨84266107521677778556118555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56177405014451852370745703 84266107521677778556118555)
    ·
      refine ⟨126399161282516667834177833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84266107521677778556118555 126399161282516667834177833)
      ·
        refine ⟨94799370961887500875633375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126399161282516667834177833 94799370961887500875633375)
        ·
          refine ⟨142199056442831251313450063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94799370961887500875633375 142199056442831251313450063)
          ·
            refine ⟨213298584664246876970175095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142199056442831251313450063 213298584664246876970175095)
            ·
              refine ⟨319947876996370315455262643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213298584664246876970175095 319947876996370315455262643)
              ·
                refine ⟨479921815494555473182893965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319947876996370315455262643 479921815494555473182893965)
                ·
                  refine ⟨179970680810458302443585237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479921815494555473182893965 179970680810458302443585237)
                  ·
                    refine ⟨4218062831495116463521529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 179970680810458302443585237 4218062831495116463521529)
                    ·
                      refine ⟨3163547123621337347641147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4218062831495116463521529 3163547123621337347641147)
                      ·
                        rfl

theorem cell23_6160986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_6160986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160986 prefixEnd_6160986 := by exact prefixLift 6160986
  have htrace : WordTrace (prefixWord ++ tailWord_6160986) baseStart_6160986 baseEnd_6160986 := by
    simpa [prefixWord, tailWord_6160986, baseEnd_6160986] using wordTrace_append hprefix tailTrace_6160986
  have hstable : (prefixWord ++ tailWord_6160986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160986).length < 2 ^ (prefixWord ++ tailWord_6160986).sum := by decide
  have hdescent : baseEnd_6160986 < baseStart_6160986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6160996 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_6160996 : Nat := 118140960795 + 6160996 * 2 ^ 59
def prefixEnd_6160996 : Nat := 4983230072969 + 3 ^ 40 * 6160996 * 2
def baseEnd_6160996 : Nat := 1054517419475960769505367

theorem tailTrace_6160996 : CollatzResearch.WordTrace tailWord_6160996 prefixEnd_6160996 1054517419475960769505367 := by
  unfold tailWord_6160996
  simp only [CollatzResearch.WordTrace]
  refine ⟨112354992393885590595423421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149806656525180787460564561 112354992393885590595423421)
  ·
    refine ⟨42133122147707096473283783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112354992393885590595423421 42133122147707096473283783)
    ·
      refine ⟨63199683221560644709925675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42133122147707096473283783 63199683221560644709925675)
      ·
        refine ⟨94799524832340967064888513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63199683221560644709925675 94799524832340967064888513)
        ·
          refine ⟨71099643624255725298666385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94799524832340967064888513 71099643624255725298666385)
          ·
            refine ⟨53324732718191793973999789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71099643624255725298666385 53324732718191793973999789)
            ·
              refine ⟨19996774769321922740249921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53324732718191793973999789 19996774769321922740249921)
              ·
                refine ⟨14997581076991442055187441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19996774769321922740249921 14997581076991442055187441)
                ·
                  refine ⟨11248185807743581541390581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14997581076991442055187441 11248185807743581541390581)
                  ·
                    refine ⟨1054517419475960769505367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11248185807743581541390581 1054517419475960769505367)
                    ·
                      rfl

theorem cell23_6160996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_6160996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6160996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6160996 prefixEnd_6160996 := by exact prefixLift 6160996
  have htrace : WordTrace (prefixWord ++ tailWord_6160996) baseStart_6160996 baseEnd_6160996 := by
    simpa [prefixWord, tailWord_6160996, baseEnd_6160996] using wordTrace_append hprefix tailTrace_6160996
  have hstable : (prefixWord ++ tailWord_6160996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6160996).length < 2 ^ (prefixWord ++ tailWord_6160996).sum := by decide
  have hdescent : baseEnd_6160996 < baseStart_6160996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6160996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161000 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 7]
def baseStart_6161000 : Nat := 118140960795 + 6161000 * 2 ^ 59
def prefixEnd_6161000 : Nat := 4983230072969 + 3 ^ 40 * 6161000 * 2
def baseEnd_6161000 : Nat := 351506034705611143651787

theorem tailTrace_6161000 : CollatzResearch.WordTrace tailWord_6161000 prefixEnd_6161000 351506034705611143651787 := by
  unfold tailWord_6161000
  simp only [CollatzResearch.WordTrace]
  refine ⟨112355065339878344936996227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149806753786504459915994969 112355065339878344936996227)
  ·
    refine ⟨168532598009817517405494341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112355065339878344936996227 168532598009817517405494341)
    ·
      refine ⟨31599862126840784513530189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168532598009817517405494341 31599862126840784513530189)
      ·
        refine ⟨11849948297565294192573821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31599862126840784513530189 11849948297565294192573821)
        ·
          refine ⟨4443730611586985322215183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11849948297565294192573821 4443730611586985322215183)
          ·
            refine ⟨6665595917380477983322775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4443730611586985322215183 6665595917380477983322775)
            ·
              refine ⟨9998393876070716974984163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6665595917380477983322775 9998393876070716974984163)
              ·
                refine ⟨14997590814106075462476245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9998393876070716974984163 14997590814106075462476245)
                ·
                  refine ⟨351506034705611143651787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14997590814106075462476245 351506034705611143651787)
                  ·
                    rfl

theorem cell23_6161000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 7].length) (baseStart_6161000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161000 prefixEnd_6161000 := by exact prefixLift 6161000
  have htrace : WordTrace (prefixWord ++ tailWord_6161000) baseStart_6161000 baseEnd_6161000 := by
    simpa [prefixWord, tailWord_6161000, baseEnd_6161000] using wordTrace_append hprefix tailTrace_6161000
  have hstable : (prefixWord ++ tailWord_6161000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161000).length < 2 ^ (prefixWord ++ tailWord_6161000).sum := by decide
  have hdescent : baseEnd_6161000 < baseStart_6161000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161006 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_6161006 : Nat := 118140960795 + 6161006 * 2 ^ 59
def prefixEnd_6161006 : Nat := 4983230072969 + 3 ^ 40 * 6161006 * 2
def baseEnd_6161006 : Nat := 3163557393234427269391055

theorem tailTrace_6161006 : CollatzResearch.WordTrace tailWord_6161006 prefixEnd_6161006 3163557393234427269391055 := by
  unfold tailWord_6161006
  simp only [CollatzResearch.WordTrace]
  refine ⟨28088793689716869112338859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149806899678489968599140581 28088793689716869112338859)
  ·
    refine ⟨42133190534575303668508289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28088793689716869112338859 42133190534575303668508289)
    ·
      refine ⟨31599892900931477751381217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42133190534575303668508289 31599892900931477751381217)
      ·
        refine ⟨23699919675698608313535913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31599892900931477751381217 23699919675698608313535913)
        ·
          refine ⟨17774939756773956235151935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23699919675698608313535913 17774939756773956235151935)
          ·
            refine ⟨26662409635160934352727903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17774939756773956235151935 26662409635160934352727903)
            ·
              refine ⟨39993614452741401529091855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26662409635160934352727903 39993614452741401529091855)
              ·
                refine ⟨59990421679112102293637783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39993614452741401529091855 59990421679112102293637783)
                ·
                  refine ⟨89985632518668153440456675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59990421679112102293637783 89985632518668153440456675)
                  ·
                    refine ⟨134978448778002230160685013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89985632518668153440456675 134978448778002230160685013)
                    ·
                      refine ⟨3163557393234427269391055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134978448778002230160685013 3163557393234427269391055)
                      ·
                        rfl

theorem cell23_6161006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_6161006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161006 prefixEnd_6161006 := by exact prefixLift 6161006
  have htrace : WordTrace (prefixWord ++ tailWord_6161006) baseStart_6161006 baseEnd_6161006 := by
    simpa [prefixWord, tailWord_6161006, baseEnd_6161006] using wordTrace_append hprefix tailTrace_6161006
  have hstable : (prefixWord ++ tailWord_6161006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161006).length < 2 ^ (prefixWord ++ tailWord_6161006).sum := by decide
  have hdescent : baseEnd_6161006 < baseStart_6161006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161053 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_6161053 : Nat := 118140960795 + 6161053 * 2 ^ 59
def prefixEnd_6161053 : Nat := 4983230072969 + 3 ^ 40 * 6161053 * 2
def baseEnd_6161053 : Nat := 3163581526825188585503339

theorem tailTrace_6161053 : CollatzResearch.WordTrace tailWord_6161053 prefixEnd_6161053 3163581526825188585503339 := by
  unfold tailWord_6161053
  simp only [CollatzResearch.WordTrace]
  refine ⟨224712063748564679925671813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149808042499043119950447875 224712063748564679925671813)
  ·
    refine ⟨42133511952855877486063465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224712063748564679925671813 42133511952855877486063465)
    ·
      refine ⟨31600133964641908114547599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42133511952855877486063465 31600133964641908114547599)
      ·
        refine ⟨47400200946962862171821399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31600133964641908114547599 47400200946962862171821399)
        ·
          refine ⟨71100301420444293257732099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47400200946962862171821399 71100301420444293257732099)
          ·
            refine ⟨106650452130666439886598149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71100301420444293257732099 106650452130666439886598149)
            ·
              refine ⟨19996959774499957478737153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106650452130666439886598149 19996959774499957478737153)
              ·
                refine ⟨14997719830874968109052865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19996959774499957478737153 14997719830874968109052865)
                ·
                  refine ⟨11248289873156226081789649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14997719830874968109052865 11248289873156226081789649)
                  ·
                    refine ⟨8436217404867169561342237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11248289873156226081789649 8436217404867169561342237)
                    ·
                      refine ⟨3163581526825188585503339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8436217404867169561342237 3163581526825188585503339)
                      ·
                        rfl

theorem cell23_6161053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_6161053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161053 prefixEnd_6161053 := by exact prefixLift 6161053
  have htrace : WordTrace (prefixWord ++ tailWord_6161053) baseStart_6161053 baseEnd_6161053 := by
    simpa [prefixWord, tailWord_6161053, baseEnd_6161053] using wordTrace_append hprefix tailTrace_6161053
  have hstable : (prefixWord ++ tailWord_6161053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161053).length < 2 ^ (prefixWord ++ tailWord_6161053).sum := by decide
  have hdescent : baseEnd_6161053 < baseStart_6161053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161060 : List Nat := [2, 3, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_6161060 : Nat := 118140960795 + 6161060 * 2 ^ 59
def prefixEnd_6161060 : Nat := 4983230072969 + 3 ^ 40 * 6161060 * 2
def baseEnd_6161060 : Nat := 1054528373729923352705269

theorem tailTrace_6161060 : CollatzResearch.WordTrace tailWord_6161060 prefixEnd_6161060 1054528373729923352705269 := by
  unfold tailWord_6161060
  simp only [CollatzResearch.WordTrace]
  refine ⟨112356159529769660060588317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149808212706359546747451089 112356159529769660060588317)
  ·
    refine ⟨42133559823663622522720619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112356159529769660060588317 42133559823663622522720619)
    ·
      refine ⟨63200339735495433784080929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42133559823663622522720619 63200339735495433784080929)
      ·
        refine ⟨47400254801621575338060697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63200339735495433784080929 47400254801621575338060697)
        ·
          refine ⟨35550191101216181503545523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47400254801621575338060697 35550191101216181503545523)
          ·
            refine ⟨53325286651824272255318285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35550191101216181503545523 53325286651824272255318285)
            ·
              refine ⟨19996982494434102095744357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53325286651824272255318285 19996982494434102095744357)
              ·
                refine ⟨3749434217706394142952067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19996982494434102095744357 3749434217706394142952067)
                ·
                  refine ⟨5624151326559591214428101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3749434217706394142952067 5624151326559591214428101)
                  ·
                    refine ⟨1054528373729923352705269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5624151326559591214428101 1054528373729923352705269)
                    ·
                      rfl

theorem cell23_6161060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_6161060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161060 prefixEnd_6161060 := by exact prefixLift 6161060
  have htrace : WordTrace (prefixWord ++ tailWord_6161060) baseStart_6161060 baseEnd_6161060 := by
    simpa [prefixWord, tailWord_6161060, baseEnd_6161060] using wordTrace_append hprefix tailTrace_6161060
  have hstable : (prefixWord ++ tailWord_6161060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161060).length < 2 ^ (prefixWord ++ tailWord_6161060).sum := by decide
  have hdescent : baseEnd_6161060 < baseStart_6161060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161136 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 6]
def baseStart_6161136 : Nat := 118140960795 + 6161136 * 2 ^ 59
def prefixEnd_6161136 : Nat := 4983230072969 + 3 ^ 40 * 6161136 * 2
def baseEnd_6161136 : Nat := 3163624145719511760765457

theorem tailTrace_6161136 : CollatzResearch.WordTrace tailWord_6161136 prefixEnd_6161136 3163624145719511760765457 := by
  unfold tailWord_6161136
  simp only [CollatzResearch.WordTrace]
  refine ⟨112357545503631992550471631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149810060671509323400628841 112357545503631992550471631)
  ·
    refine ⟨168536318255447988825707447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112357545503631992550471631 168536318255447988825707447)
    ·
      refine ⟨252804477383171983238561171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168536318255447988825707447 252804477383171983238561171)
      ·
        refine ⟨379206716074757974857841757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252804477383171983238561171 379206716074757974857841757)
        ·
          refine ⟨142202518528034240571690659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379206716074757974857841757 142202518528034240571690659)
          ·
            refine ⟨213303777792051360857535989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142202518528034240571690659 213303777792051360857535989)
            ·
              refine ⟨19997229168004815080393999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213303777792051360857535989 19997229168004815080393999)
              ·
                refine ⟨29995843752007222620590999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19997229168004815080393999 29995843752007222620590999)
                ·
                  refine ⟨44993765628010833930886499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29995843752007222620590999 44993765628010833930886499)
                  ·
                    refine ⟨67490648442016250896329749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44993765628010833930886499 67490648442016250896329749)
                    ·
                      refine ⟨3163624145719511760765457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67490648442016250896329749 3163624145719511760765457)
                      ·
                        rfl

theorem cell23_6161136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_6161136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161136 prefixEnd_6161136 := by exact prefixLift 6161136
  have htrace : WordTrace (prefixWord ++ tailWord_6161136) baseStart_6161136 baseEnd_6161136 := by
    simpa [prefixWord, tailWord_6161136, baseEnd_6161136] using wordTrace_append hprefix tailTrace_6161136
  have hstable : (prefixWord ++ tailWord_6161136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161136).length < 2 ^ (prefixWord ++ tailWord_6161136).sum := by decide
  have hdescent : baseEnd_6161136 < baseStart_6161136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161150 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_6161150 : Nat := 118140960795 + 6161150 * 2 ^ 59
def prefixEnd_6161150 : Nat := 4983230072969 + 3 ^ 40 * 6161150 * 2
def baseEnd_6161150 : Nat := 1054543778149558235330131

theorem tailTrace_6161150 : CollatzResearch.WordTrace tailWord_6161150 prefixEnd_6161150 1054543778149558235330131 := by
  unfold tailWord_6161150
  simp only [CollatzResearch.WordTrace]
  refine ⟨28089450203651658186494113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149810401086142176994635269 28089450203651658186494113)
  ·
    refine ⟨21067087652738743639870585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28089450203651658186494113 21067087652738743639870585)
    ·
      refine ⟨15800315739554057729902939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21067087652738743639870585 15800315739554057729902939)
      ·
        refine ⟨23700473609331086594854409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15800315739554057729902939 23700473609331086594854409)
        ·
          refine ⟨17775355206998314946140807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23700473609331086594854409 17775355206998314946140807)
          ·
            refine ⟨26663032810497472419211211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17775355206998314946140807 26663032810497472419211211)
            ·
              refine ⟨39994549215746208628816817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26663032810497472419211211 39994549215746208628816817)
              ·
                refine ⟨29995911911809656471612613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39994549215746208628816817 29995911911809656471612613)
                ·
                  refine ⟨5624233483464310588427365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29995911911809656471612613 5624233483464310588427365)
                  ·
                    refine ⟨1054543778149558235330131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5624233483464310588427365 1054543778149558235330131)
                    ·
                      rfl

theorem cell23_6161150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_6161150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161150 prefixEnd_6161150 := by exact prefixLift 6161150
  have htrace : WordTrace (prefixWord ++ tailWord_6161150) baseStart_6161150 baseEnd_6161150 := by
    simpa [prefixWord, tailWord_6161150, baseEnd_6161150] using wordTrace_append hprefix tailTrace_6161150
  have hstable : (prefixWord ++ tailWord_6161150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161150).length < 2 ^ (prefixWord ++ tailWord_6161150).sum := by decide
  have hdescent : baseEnd_6161150 < baseStart_6161150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161160 : List Nat := [2, 1, 3, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_6161160 : Nat := 118140960795 + 6161160 * 2 ^ 59
def prefixEnd_6161160 : Nat := 4983230072969 + 3 ^ 40 * 6161160 * 2
def baseEnd_6161160 : Nat := 3163636469255219666865347

theorem tailTrace_6161160 : CollatzResearch.WordTrace tailWord_6161160 prefixEnd_6161160 3163636469255219666865347 := by
  unfold tailWord_6161160
  simp only [CollatzResearch.WordTrace]
  refine ⟨112357983179588518599908467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149810644239451358133211289 112357983179588518599908467)
  ·
    refine ⟨168536974769382777899862701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112357983179588518599908467 168536974769382777899862701)
    ·
      refine ⟨63201365538518541712448513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168536974769382777899862701 63201365538518541712448513)
      ·
        refine ⟨47401024153888906284336385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63201365538518541712448513 47401024153888906284336385)
        ·
          refine ⟨35550768115416679713252289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47401024153888906284336385 35550768115416679713252289)
          ·
            refine ⟨26663076086562509784939217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35550768115416679713252289 26663076086562509784939217)
            ·
              refine ⟨19997307064921882338704413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26663076086562509784939217 19997307064921882338704413)
              ·
                refine ⟨7498990149345705877014155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19997307064921882338704413 7498990149345705877014155)
                ·
                  refine ⟨11248485224018558815521233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7498990149345705877014155 11248485224018558815521233)
                  ·
                    refine ⟨8436363918013919111640925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11248485224018558815521233 8436363918013919111640925)
                    ·
                      refine ⟨3163636469255219666865347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8436363918013919111640925 3163636469255219666865347)
                      ·
                        rfl

theorem cell23_6161160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_6161160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161160 prefixEnd_6161160 := by exact prefixLift 6161160
  have htrace : WordTrace (prefixWord ++ tailWord_6161160) baseStart_6161160 baseEnd_6161160 := by
    simpa [prefixWord, tailWord_6161160, baseEnd_6161160] using wordTrace_append hprefix tailTrace_6161160
  have hstable : (prefixWord ++ tailWord_6161160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161160).length < 2 ^ (prefixWord ++ tailWord_6161160).sum := by decide
  have hdescent : baseEnd_6161160 < baseStart_6161160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161176 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 2, 7]
def baseStart_6161176 : Nat := 118140960795 + 6161176 * 2 ^ 59
def prefixEnd_6161176 : Nat := 4983230072969 + 3 ^ 40 * 6161176 * 2
def baseEnd_6161176 : Nat := 1054548228315230534755091

theorem tailTrace_6161176 : CollatzResearch.WordTrace tailWord_6161176 prefixEnd_6161176 1054548228315230534755091 := by
  unfold tailWord_6161176
  simp only [CollatzResearch.WordTrace]
  refine ⟨112358274963559535966199691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149811033284746047954932921 112358274963559535966199691)
  ·
    refine ⟨168537412445339303949299537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112358274963559535966199691 168537412445339303949299537)
    ·
      refine ⟨126403059334004477961974653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168537412445339303949299537 126403059334004477961974653)
      ·
        refine ⟨47401147250251679235740495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126403059334004477961974653 47401147250251679235740495)
        ·
          refine ⟨71101720875377518853610743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47401147250251679235740495 71101720875377518853610743)
          ·
            refine ⟨106652581313066278280416115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71101720875377518853610743 106652581313066278280416115)
            ·
              refine ⟨159978871969599417420624173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106652581313066278280416115 159978871969599417420624173)
              ·
                refine ⟨59992076988599781532734065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159978871969599417420624173 59992076988599781532734065)
                ·
                  refine ⟨44994057741449836149550549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59992076988599781532734065 44994057741449836149550549)
                  ·
                    refine ⟨1054548228315230534755091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44994057741449836149550549 1054548228315230534755091)
                    ·
                      rfl

theorem cell23_6161176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_6161176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161176 prefixEnd_6161176 := by exact prefixLift 6161176
  have htrace : WordTrace (prefixWord ++ tailWord_6161176) baseStart_6161176 baseEnd_6161176 := by
    simpa [prefixWord, tailWord_6161176, baseEnd_6161176] using wordTrace_append hprefix tailTrace_6161176
  have hstable : (prefixWord ++ tailWord_6161176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161176).length < 2 ^ (prefixWord ++ tailWord_6161176).sum := by decide
  have hdescent : baseEnd_6161176 < baseStart_6161176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161247 : List Nat := [1, 1, 2, 3, 1, 3, 1, 5, 2, 2, 2]
def baseStart_6161247 : Nat := 118140960795 + 6161247 * 2 ^ 59
def prefixEnd_6161247 : Nat := 4983230072969 + 3 ^ 40 * 6161247 * 2
def baseEnd_6161247 : Nat := 3163681142072160826477447

theorem tailTrace_6161247 : CollatzResearch.WordTrace tailWord_6161247 prefixEnd_6161247 3163681142072160826477447 := by
  unfold tailWord_6161247
  simp only [CollatzResearch.WordTrace]
  refine ⟨224719139509861851058233995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149812759673241234038822663 224719139509861851058233995)
  ·
    refine ⟨337078709264792776587350993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224719139509861851058233995 337078709264792776587350993)
    ·
      refine ⟨252809031948594582440513245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337078709264792776587350993 252809031948594582440513245)
      ·
        refine ⟨94803386980722968415192467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252809031948594582440513245 94803386980722968415192467)
        ·
          refine ⟨142205080471084452622788701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94803386980722968415192467 142205080471084452622788701)
          ·
            refine ⟨53326905176656669733545763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142205080471084452622788701 53326905176656669733545763)
            ·
              refine ⟨79990357764985004600318645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53326905176656669733545763 79990357764985004600318645)
              ·
                refine ⟨7499096040467344181279873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79990357764985004600318645 7499096040467344181279873)
                ·
                  refine ⟨5624322030350508135959905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7499096040467344181279873 5624322030350508135959905)
                  ·
                    refine ⟨4218241522762881101969929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5624322030350508135959905 4218241522762881101969929)
                    ·
                      refine ⟨3163681142072160826477447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4218241522762881101969929 3163681142072160826477447)
                      ·
                        rfl

theorem cell23_6161247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_6161247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161247 prefixEnd_6161247 := by exact prefixLift 6161247
  have htrace : WordTrace (prefixWord ++ tailWord_6161247) baseStart_6161247 baseEnd_6161247 := by
    simpa [prefixWord, tailWord_6161247, baseEnd_6161247] using wordTrace_append hprefix tailTrace_6161247
  have hstable : (prefixWord ++ tailWord_6161247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161247).length < 2 ^ (prefixWord ++ tailWord_6161247).sum := by decide
  have hdescent : baseEnd_6161247 < baseStart_6161247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161283 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 4, 5]
def baseStart_6161283 : Nat := 118140960795 + 6161283 * 2 ^ 59
def prefixEnd_6161283 : Nat := 4983230072969 + 3 ^ 40 * 6161283 * 2
def baseEnd_6161283 : Nat := 1054566542458574228542427

theorem tailTrace_6161283 : CollatzResearch.WordTrace tailWord_6161283 prefixEnd_6161283 1054566542458574228542427 := by
  unfold tailWord_6161283
  simp only [CollatzResearch.WordTrace]
  refine ⟨224720452537731429206544503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149813635025154286137696335 224720452537731429206544503)
  ·
    refine ⟨337080678806597143809816755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224720452537731429206544503 337080678806597143809816755)
    ·
      refine ⟨505621018209895715714725133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337080678806597143809816755 505621018209895715714725133)
      ·
        refine ⟨189607881828710893393021925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 505621018209895715714725133 189607881828710893393021925)
        ·
          refine ⟨35551477842883292511191611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189607881828710893393021925 35551477842883292511191611)
          ·
            refine ⟨53327216764324938766787417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35551477842883292511191611 53327216764324938766787417)
            ·
              refine ⟨39995412573243704075090563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53327216764324938766787417 39995412573243704075090563)
              ·
                refine ⟨59993118859865556112635845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39995412573243704075090563 59993118859865556112635845)
                ·
                  refine ⟨11248709786224791771119221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59993118859865556112635845 11248709786224791771119221)
                  ·
                    refine ⟨1054566542458574228542427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11248709786224791771119221 1054566542458574228542427)
                    ·
                      rfl

theorem cell23_6161283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 5].length) (baseStart_6161283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161283 prefixEnd_6161283 := by exact prefixLift 6161283
  have htrace : WordTrace (prefixWord ++ tailWord_6161283) baseStart_6161283 baseEnd_6161283 := by
    simpa [prefixWord, tailWord_6161283, baseEnd_6161283] using wordTrace_append hprefix tailTrace_6161283
  have hstable : (prefixWord ++ tailWord_6161283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161283).length < 2 ^ (prefixWord ++ tailWord_6161283).sum := by decide
  have hdescent : baseEnd_6161283 < baseStart_6161283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161298 : List Nat := [3, 2, 3, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_6161298 : Nat := 118140960795 + 6161298 * 2 ^ 59
def prefixEnd_6161298 : Nat := 4983230072969 + 3 ^ 40 * 6161298 * 2
def baseEnd_6161298 : Nat := 3163707329585540126939713

theorem tailTrace_6161298 : CollatzResearch.WordTrace tailWord_6161298 prefixEnd_6161298 3163707329585540126939713 := by
  unfold tailWord_6161298
  simp only [CollatzResearch.WordTrace]
  refine ⟨56180249908169271692085137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149813999755118057845560365 56180249908169271692085137)
  ·
    refine ⟨42135187431126953769063853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56180249908169271692085137 42135187431126953769063853)
    ·
      refine ⟨15800695286672607663398945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42135187431126953769063853 15800695286672607663398945)
      ·
        refine ⟨11850521465004455747549209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15800695286672607663398945 11850521465004455747549209)
        ·
          refine ⟨8887891098753341810661907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11850521465004455747549209 8887891098753341810661907)
          ·
            refine ⟨13331836648130012715992861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8887891098753341810661907 13331836648130012715992861)
            ·
              refine ⟨4999438743048754768497323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13331836648130012715992861 4999438743048754768497323)
              ·
                refine ⟨7499158114573132152745985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4999438743048754768497323 7499158114573132152745985)
                ·
                  refine ⟨5624368585929849114559489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7499158114573132152745985 5624368585929849114559489)
                  ·
                    refine ⟨4218276439447386835919617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5624368585929849114559489 4218276439447386835919617)
                    ·
                      refine ⟨3163707329585540126939713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4218276439447386835919617 3163707329585540126939713)
                      ·
                        rfl

theorem cell23_6161298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_6161298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161298 prefixEnd_6161298 := by exact prefixLift 6161298
  have htrace : WordTrace (prefixWord ++ tailWord_6161298) baseStart_6161298 baseEnd_6161298 := by
    simpa [prefixWord, tailWord_6161298, baseEnd_6161298] using wordTrace_append hprefix tailTrace_6161298
  have hstable : (prefixWord ++ tailWord_6161298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161298).length < 2 ^ (prefixWord ++ tailWord_6161298).sum := by decide
  have hdescent : baseEnd_6161298 < baseStart_6161298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161303 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_6161303 : Nat := 118140960795 + 6161303 * 2 ^ 59
def prefixEnd_6161303 : Nat := 4983230072969 + 3 ^ 40 * 6161303 * 2
def baseEnd_6161303 : Nat := 3163709896988812607377189

theorem tailTrace_6161303 : CollatzResearch.WordTrace tailWord_6161303 prefixEnd_6161303 3163709896988812607377189 := by
  unfold tailWord_6161303
  simp only [CollatzResearch.WordTrace]
  refine ⟨224721181997658972622272563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149814121331772648414848375 224721181997658972622272563)
  ·
    refine ⟨337081772996488458933408845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224721181997658972622272563 337081772996488458933408845)
    ·
      refine ⟨126405664873683172100028317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337081772996488458933408845 126405664873683172100028317)
      ·
        refine ⟨47402124327631189537510619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126405664873683172100028317 47402124327631189537510619)
        ·
          refine ⟨71103186491446784306265929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47402124327631189537510619 71103186491446784306265929)
          ·
            refine ⟨53327389868585088229699447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71103186491446784306265929 53327389868585088229699447)
            ·
              refine ⟨79991084802877632344549171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53327389868585088229699447 79991084802877632344549171)
              ·
                refine ⟨119986627204316448516823757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79991084802877632344549171 119986627204316448516823757)
                ·
                  refine ⟨44994985201618668193808909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119986627204316448516823757 44994985201618668193808909)
                  ·
                    refine ⟨16873119450607000572678341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44994985201618668193808909 16873119450607000572678341)
                    ·
                      refine ⟨3163709896988812607377189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16873119450607000572678341 3163709896988812607377189)
                      ·
                        rfl

theorem cell23_6161303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_6161303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161303 prefixEnd_6161303 := by exact prefixLift 6161303
  have htrace : WordTrace (prefixWord ++ tailWord_6161303) baseStart_6161303 baseEnd_6161303 := by
    simpa [prefixWord, tailWord_6161303, baseEnd_6161303] using wordTrace_append hprefix tailTrace_6161303
  have hstable : (prefixWord ++ tailWord_6161303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161303).length < 2 ^ (prefixWord ++ tailWord_6161303).sum := by decide
  have hdescent : baseEnd_6161303 < baseStart_6161303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161394 : List Nat := [3, 2, 1, 5, 1, 1, 2, 2, 6]
def baseStart_6161394 : Nat := 118140960795 + 6161394 * 2 ^ 59
def prefixEnd_6161394 : Nat := 4983230072969 + 3 ^ 40 * 6161394 * 2
def baseEnd_6161394 : Nat := 351528513747596861259919

theorem tailTrace_6161394 : CollatzResearch.WordTrace tailWord_6161394 prefixEnd_6161394 351528513747596861259919 := by
  unfold tailWord_6161394
  simp only [CollatzResearch.WordTrace]
  refine ⟨56181125260082323790958809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149816334026886196775890157 56181125260082323790958809)
  ·
    refine ⟨42135843945061742843219107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56181125260082323790958809 42135843945061742843219107)
    ·
      refine ⟨63203765917592614264828661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42135843945061742843219107 63203765917592614264828661)
      ·
        refine ⟨5925353054774307587327687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63203765917592614264828661 5925353054774307587327687)
        ·
          refine ⟨8888029582161461380991531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5925353054774307587327687 8888029582161461380991531)
          ·
            refine ⟨13332044373242192071487297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8888029582161461380991531 13332044373242192071487297)
            ·
              refine ⟨9999033279931644053615473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13332044373242192071487297 9999033279931644053615473)
              ·
                refine ⟨7499274959948733040211605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9999033279931644053615473 7499274959948733040211605)
                ·
                  refine ⟨351528513747596861259919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7499274959948733040211605 351528513747596861259919)
                  ·
                    rfl

theorem cell23_6161394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_6161394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161394 prefixEnd_6161394 := by exact prefixLift 6161394
  have htrace : WordTrace (prefixWord ++ tailWord_6161394) baseStart_6161394 baseEnd_6161394 := by
    simpa [prefixWord, tailWord_6161394, baseEnd_6161394] using wordTrace_append hprefix tailTrace_6161394
  have hstable : (prefixWord ++ tailWord_6161394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161394).length < 2 ^ (prefixWord ++ tailWord_6161394).sum := by decide
  have hdescent : baseEnd_6161394 < baseStart_6161394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161398 : List Nat := [5, 1, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_6161398 : Nat := 118140960795 + 6161398 * 2 ^ 59
def prefixEnd_6161398 : Nat := 4983230072969 + 3 ^ 40 * 6161398 * 2
def baseEnd_6161398 : Nat := 1054586225883663245229751

theorem tailTrace_6161398 : CollatzResearch.WordTrace tailWord_6161398 prefixEnd_6161398 1054586225883663245229751 := by
  unfold tailWord_6161398
  simp only [CollatzResearch.WordTrace]
  refine ⟨14045290433269675240436303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149816431288209869231320565 14045290433269675240436303)
  ·
    refine ⟨21067935649904512860654455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14045290433269675240436303 21067935649904512860654455)
    ·
      refine ⟨31601903474856769290981683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21067935649904512860654455 31601903474856769290981683)
      ·
        refine ⟨47402855212285153936472525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31601903474856769290981683 47402855212285153936472525)
        ·
          refine ⟨17776070704606932726177197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47402855212285153936472525 17776070704606932726177197)
          ·
            refine ⟨6666026514227599772316449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17776070704606932726177197 6666026514227599772316449)
            ·
              refine ⟨4999519885670699829237337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6666026514227599772316449 4999519885670699829237337)
              ·
                refine ⟨3749639914253024871928003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4999519885670699829237337 3749639914253024871928003)
                ·
                  refine ⟨5624459871379537307892005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3749639914253024871928003 5624459871379537307892005)
                  ·
                    refine ⟨1054586225883663245229751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5624459871379537307892005 1054586225883663245229751)
                    ·
                      rfl

theorem cell23_6161398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_6161398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161398 prefixEnd_6161398 := by exact prefixLift 6161398
  have htrace : WordTrace (prefixWord ++ tailWord_6161398) baseStart_6161398 baseEnd_6161398 := by
    simpa [prefixWord, tailWord_6161398, baseEnd_6161398] using wordTrace_append hprefix tailTrace_6161398
  have hstable : (prefixWord ++ tailWord_6161398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161398).length < 2 ^ (prefixWord ++ tailWord_6161398).sum := by decide
  have hdescent : baseEnd_6161398 < baseStart_6161398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161403 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 5, 6]
def baseStart_6161403 : Nat := 118140960795 + 6161403 * 2 ^ 59
def prefixEnd_6161403 : Nat := 4983230072969 + 3 ^ 40 * 6161403 * 2
def baseEnd_6161403 : Nat := 1054587081684754072042243

theorem tailTrace_6161403 : CollatzResearch.WordTrace tailWord_6161403 prefixEnd_6161403 1054587081684754072042243 := by
  unfold tailWord_6161403
  simp only [CollatzResearch.WordTrace]
  refine ⟨224724829297296689700912863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149816552864864459800608575 224724829297296689700912863)
  ·
    refine ⟨337087243945945034551369295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224724829297296689700912863 337087243945945034551369295)
    ·
      refine ⟨505630865918917551827053943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337087243945945034551369295 505630865918917551827053943)
      ·
        refine ⟨758446298878376327740580915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505630865918917551827053943 758446298878376327740580915)
        ·
          refine ⟨1137669448317564491610871373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758446298878376327740580915 1137669448317564491610871373)
          ·
            refine ⟨426626043119086684354076765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1137669448317564491610871373 426626043119086684354076765)
            ·
              refine ⟨159984766169657506632778787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426626043119086684354076765 159984766169657506632778787)
              ·
                refine ⟨239977149254486259949168181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159984766169657506632778787 239977149254486259949168181)
                ·
                  refine ⟨22497857742608086870234517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239977149254486259949168181 22497857742608086870234517)
                  ·
                    refine ⟨1054587081684754072042243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22497857742608086870234517 1054587081684754072042243)
                    ·
                      rfl

theorem cell23_6161403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 6].length) (baseStart_6161403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161403 prefixEnd_6161403 := by exact prefixLift 6161403
  have htrace : WordTrace (prefixWord ++ tailWord_6161403) baseStart_6161403 baseEnd_6161403 := by
    simpa [prefixWord, tailWord_6161403, baseEnd_6161403] using wordTrace_append hprefix tailTrace_6161403
  have hstable : (prefixWord ++ tailWord_6161403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161403).length < 2 ^ (prefixWord ++ tailWord_6161403).sum := by decide
  have hdescent : baseEnd_6161403 < baseStart_6161403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161420 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 1, 6]
def baseStart_6161420 : Nat := 118140960795 + 6161420 * 2 ^ 59
def prefixEnd_6161420 : Nat := 4983230072969 + 3 ^ 40 * 6161420 * 2
def baseEnd_6161420 : Nat := 1054589991408462883204717

theorem tailTrace_6161420 : CollatzResearch.WordTrace tailWord_6161420 prefixEnd_6161420 1054589991408462883204717 := by
  unfold tailWord_6161420
  simp only [CollatzResearch.WordTrace]
  refine ⟨112362724669117550802140857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149816966225490067736187809 112362724669117550802140857)
  ·
    refine ⟨84272043501838163101605643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112362724669117550802140857 84272043501838163101605643)
    ·
      refine ⟨126408065252757244652408465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84272043501838163101605643 126408065252757244652408465)
      ·
        refine ⟨94806048939567933489306349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126408065252757244652408465 94806048939567933489306349)
        ·
          refine ⟨35552268352337975058489881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94806048939567933489306349 35552268352337975058489881)
          ·
            refine ⟨26664201264253481293867411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35552268352337975058489881 26664201264253481293867411)
            ·
              refine ⟨39996301896380221940801117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26664201264253481293867411 39996301896380221940801117)
              ·
                refine ⟨14998613211142583227800419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39996301896380221940801117 14998613211142583227800419)
                ·
                  refine ⟨22497919816713874841700629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14998613211142583227800419 22497919816713874841700629)
                  ·
                    refine ⟨1054589991408462883204717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22497919816713874841700629 1054589991408462883204717)
                    ·
                      rfl

theorem cell23_6161420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_6161420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161420 prefixEnd_6161420 := by exact prefixLift 6161420
  have htrace : WordTrace (prefixWord ++ tailWord_6161420) baseStart_6161420 baseEnd_6161420 := by
    simpa [prefixWord, tailWord_6161420, baseEnd_6161420] using wordTrace_append hprefix tailTrace_6161420
  have hstable : (prefixWord ++ tailWord_6161420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161420).length < 2 ^ (prefixWord ++ tailWord_6161420).sum := by decide
  have hdescent : baseEnd_6161420 < baseStart_6161420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161431 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 2, 3, 2]
def baseStart_6161431 : Nat := 118140960795 + 6161431 * 2 ^ 59
def prefixEnd_6161431 : Nat := 4983230072969 + 3 ^ 40 * 6161431 * 2
def baseEnd_6161431 : Nat := 3163775622512588106576601

theorem tailTrace_6161431 : CollatzResearch.WordTrace tailWord_6161431 prefixEnd_6161431 3163775622512588106576601 := by
  unfold tailWord_6161431
  simp only [CollatzResearch.WordTrace]
  refine ⟨224725850541195250482932147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149817233694130166988621431 224725850541195250482932147)
  ·
    refine ⟨337088775811792875724398221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224725850541195250482932147 337088775811792875724398221)
    ·
      refine ⟨126408290929422328396649333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337088775811792875724398221 126408290929422328396649333)
      ·
        refine ⟨11850777274633343287185875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126408290929422328396649333 11850777274633343287185875)
        ·
          refine ⟨17776165911950014930778813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11850777274633343287185875 17776165911950014930778813)
          ·
            refine ⟨6666062216981255599042055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17776165911950014930778813 6666062216981255599042055)
            ·
              refine ⟨9999093325471883398563083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6666062216981255599042055 9999093325471883398563083)
              ·
                refine ⟨14998639988207825097844625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9999093325471883398563083 14998639988207825097844625)
                ·
                  refine ⟨11248979991155868823383469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14998639988207825097844625 11248979991155868823383469)
                  ·
                    refine ⟨4218367496683450808768801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11248979991155868823383469 4218367496683450808768801)
                    ·
                      refine ⟨3163775622512588106576601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4218367496683450808768801 3163775622512588106576601)
                      ·
                        rfl

theorem cell23_6161431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_6161431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161431 prefixEnd_6161431 := by exact prefixLift 6161431
  have htrace : WordTrace (prefixWord ++ tailWord_6161431) baseStart_6161431 baseEnd_6161431 := by
    simpa [prefixWord, tailWord_6161431, baseEnd_6161431] using wordTrace_append hprefix tailTrace_6161431
  have hstable : (prefixWord ++ tailWord_6161431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161431).length < 2 ^ (prefixWord ++ tailWord_6161431).sum := by decide
  have hdescent : baseEnd_6161431 < baseStart_6161431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161433 : List Nat := [1, 2, 1, 2, 1, 1, 4, 11]
def baseStart_6161433 : Nat := 118140960795 + 6161433 * 2 ^ 59
def prefixEnd_6161433 : Nat := 4983230072969 + 3 ^ 40 * 6161433 * 2
def baseEnd_6161433 : Nat := 117176912943477670324133

theorem tailTrace_6161433 : CollatzResearch.WordTrace tailWord_6161433 prefixEnd_6161433 117176912943477670324133 := by
  unfold tailWord_6161433
  simp only [CollatzResearch.WordTrace]
  refine ⟨224725923487188004824504953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149817282324792003216336635 224725923487188004824504953)
  ·
    refine ⟨168544442615391003618378715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224725923487188004824504953 168544442615391003618378715)
    ·
      refine ⟨252816663923086505427568073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168544442615391003618378715 252816663923086505427568073)
      ·
        refine ⟨189612497942314879070676055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252816663923086505427568073 189612497942314879070676055)
        ·
          refine ⟨284418746913472318606014083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189612497942314879070676055 284418746913472318606014083)
          ·
            refine ⟨426628120370208477909021125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284418746913472318606014083 426628120370208477909021125)
            ·
              refine ⟨79992772569414089607941461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 426628120370208477909021125 79992772569414089607941461)
              ·
                refine ⟨117176912943477670324133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 79992772569414089607941461 117176912943477670324133)
                ·
                  rfl

theorem cell23_6161433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 11].length) (baseStart_6161433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161433 prefixEnd_6161433 := by exact prefixLift 6161433
  have htrace : WordTrace (prefixWord ++ tailWord_6161433) baseStart_6161433 baseEnd_6161433 := by
    simpa [prefixWord, tailWord_6161433, baseEnd_6161433] using wordTrace_append hprefix tailTrace_6161433
  have hstable : (prefixWord ++ tailWord_6161433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161433).length < 2 ^ (prefixWord ++ tailWord_6161433).sum := by decide
  have hdescent : baseEnd_6161433 < baseStart_6161433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161444 : List Nat := [2, 3, 1, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_6161444 : Nat := 118140960795 + 6161444 * 2 ^ 59
def prefixEnd_6161444 : Nat := 4983230072969 + 3 ^ 40 * 6161444 * 2
def baseEnd_6161444 : Nat := 3163782297761096555714041

theorem tailTrace_6161444 : CollatzResearch.WordTrace tailWord_6161444 prefixEnd_6161444 3163782297761096555714041 := by
  unfold tailWord_6161444
  simp only [CollatzResearch.WordTrace]
  refine ⟨112363162345074076851577693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149817549793432102468770257 112363162345074076851577693)
  ·
    refine ⟨42136185879402778819341635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112363162345074076851577693 42136185879402778819341635)
    ·
      refine ⟨63204278819104168229012453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42136185879402778819341635 63204278819104168229012453)
      ·
        refine ⟨11850802278582031542939835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63204278819104168229012453 11850802278582031542939835)
        ·
          refine ⟨17776203417873047314409753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11850802278582031542939835 17776203417873047314409753)
          ·
            refine ⟨13332152563404785485807315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17776203417873047314409753 13332152563404785485807315)
            ·
              refine ⟨19998228845107178228710973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13332152563404785485807315 19998228845107178228710973)
              ·
                refine ⟨7499335816915191835766615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19998228845107178228710973 7499335816915191835766615)
                ·
                  refine ⟨11249003725372787753649923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7499335816915191835766615 11249003725372787753649923)
                  ·
                    refine ⟨16873505588059181630474885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11249003725372787753649923 16873505588059181630474885)
                    ·
                      refine ⟨3163782297761096555714041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16873505588059181630474885 3163782297761096555714041)
                      ·
                        rfl

theorem cell23_6161444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_6161444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161444 prefixEnd_6161444 := by exact prefixLift 6161444
  have htrace : WordTrace (prefixWord ++ tailWord_6161444) baseStart_6161444 baseEnd_6161444 := by
    simpa [prefixWord, tailWord_6161444, baseEnd_6161444] using wordTrace_append hprefix tailTrace_6161444
  have hstable : (prefixWord ++ tailWord_6161444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161444).length < 2 ^ (prefixWord ++ tailWord_6161444).sum := by decide
  have hdescent : baseEnd_6161444 < baseStart_6161444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161477 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 1, 3, 3]
def baseStart_6161477 : Nat := 118140960795 + 6161477 * 2 ^ 59
def prefixEnd_6161477 : Nat := 4983230072969 + 3 ^ 40 * 6161477 * 2
def baseEnd_6161477 : Nat := 3163799242622694926601389

theorem tailTrace_6161477 : CollatzResearch.WordTrace tailWord_6161477 prefixEnd_6161477 3163799242622694926601389 := by
  unfold tailWord_6161477
  simp only [CollatzResearch.WordTrace]
  refine ⟨224727528299028600339106685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149818352199352400226071123 224727528299028600339106685)
  ·
    refine ⟨84272823112135725127165007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224727528299028600339106685 84272823112135725127165007)
    ·
      refine ⟨126409234668203587690747511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84272823112135725127165007 126409234668203587690747511)
      ·
        refine ⟨189613852002305381536121267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126409234668203587690747511 189613852002305381536121267)
        ·
          refine ⟨284420778003458072304181901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189613852002305381536121267 284420778003458072304181901)
          ·
            refine ⟨106657791751296777114068213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284420778003458072304181901 106657791751296777114068213)
            ·
              refine ⟨9999167976684072854443895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106657791751296777114068213 9999167976684072854443895)
              ·
                refine ⟨14998751965026109281665843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9999167976684072854443895 14998751965026109281665843)
                ·
                  refine ⟨22498127947539163922498765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14998751965026109281665843 22498127947539163922498765)
                  ·
                    refine ⟨8436797980327186470937037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22498127947539163922498765 8436797980327186470937037)
                    ·
                      refine ⟨3163799242622694926601389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8436797980327186470937037 3163799242622694926601389)
                      ·
                        rfl

theorem cell23_6161477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_6161477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161477 prefixEnd_6161477 := by exact prefixLift 6161477
  have htrace : WordTrace (prefixWord ++ tailWord_6161477) baseStart_6161477 baseEnd_6161477 := by
    simpa [prefixWord, tailWord_6161477, baseEnd_6161477] using wordTrace_append hprefix tailTrace_6161477
  have hstable : (prefixWord ++ tailWord_6161477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161477).length < 2 ^ (prefixWord ++ tailWord_6161477).sum := by decide
  have hdescent : baseEnd_6161477 < baseStart_6161477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161478 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_6161478 : Nat := 118140960795 + 6161478 * 2 ^ 59
def prefixEnd_6161478 : Nat := 4983230072969 + 3 ^ 40 * 6161478 * 2
def baseEnd_6161478 : Nat := 3163799756103349422688885

theorem tailTrace_6161478 : CollatzResearch.WordTrace tailWord_6161478 prefixEnd_6161478 3163799756103349422688885 := by
  unfold tailWord_6161478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7022736399125780547184159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149818376514683318339928725 7022736399125780547184159)
  ·
    refine ⟨10534104598688670820776239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7022736399125780547184159 10534104598688670820776239)
    ·
      refine ⟨15801156898033006231164359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10534104598688670820776239 15801156898033006231164359)
      ·
        refine ⟨23701735347049509346746539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15801156898033006231164359 23701735347049509346746539)
        ·
          refine ⟨35552603020574264020119809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23701735347049509346746539 35552603020574264020119809)
          ·
            refine ⟨26664452265430698015089857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35552603020574264020119809 26664452265430698015089857)
            ·
              refine ⟨19998339199073023511317393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26664452265430698015089857 19998339199073023511317393)
              ·
                refine ⟨14998754399304767633488045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19998339199073023511317393 14998754399304767633488045)
                ·
                  refine ⟨5624532899739287862558017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14998754399304767633488045 5624532899739287862558017)
                  ·
                    refine ⟨4218399674804465896918513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5624532899739287862558017 4218399674804465896918513)
                    ·
                      refine ⟨3163799756103349422688885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4218399674804465896918513 3163799756103349422688885)
                      ·
                        rfl

theorem cell23_6161478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_6161478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161478 prefixEnd_6161478 := by exact prefixLift 6161478
  have htrace : WordTrace (prefixWord ++ tailWord_6161478) baseStart_6161478 baseEnd_6161478 := by
    simpa [prefixWord, tailWord_6161478, baseEnd_6161478] using wordTrace_append hprefix tailTrace_6161478
  have hstable : (prefixWord ++ tailWord_6161478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161478).length < 2 ^ (prefixWord ++ tailWord_6161478).sum := by decide
  have hdescent : baseEnd_6161478 < baseStart_6161478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161504 : List Nat := [2, 1, 1, 3, 2, 2, 1, 5, 1, 3, 2]
def baseStart_6161504 : Nat := 118140960795 + 6161504 * 2 ^ 59
def prefixEnd_6161504 : Nat := 4983230072969 + 3 ^ 40 * 6161504 * 2
def baseEnd_6161504 : Nat := 3163813106600366320963765

theorem tailTrace_6161504 : CollatzResearch.WordTrace tailWord_6161504 prefixEnd_6161504 3163813106600366320963765 := by
  unfold tailWord_6161504
  simp only [CollatzResearch.WordTrace]
  refine ⟨112364256534965391975169783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149819008713287189300226377 112364256534965391975169783)
  ·
    refine ⟨168546384802448087962754675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112364256534965391975169783 168546384802448087962754675)
    ·
      refine ⟨252819577203672131944132013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168546384802448087962754675 252819577203672131944132013)
      ·
        refine ⟨94807341451377049479049505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252819577203672131944132013 94807341451377049479049505)
        ·
          refine ⟨71105506088532787109287129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94807341451377049479049505 71105506088532787109287129)
          ·
            refine ⟨53329129566399590331965347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71105506088532787109287129 53329129566399590331965347)
            ·
              refine ⟨79993694349599385497948021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53329129566399590331965347 79993694349599385497948021)
              ·
                refine ⟨7499408845274942390432627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79993694349599385497948021 7499408845274942390432627)
                ·
                  refine ⟨11249113267912413585648941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7499408845274942390432627 11249113267912413585648941)
                  ·
                    refine ⟨4218417475467155094618353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11249113267912413585648941 4218417475467155094618353)
                    ·
                      refine ⟨3163813106600366320963765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4218417475467155094618353 3163813106600366320963765)
                      ·
                        rfl

theorem cell23_6161504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_6161504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161504 prefixEnd_6161504 := by exact prefixLift 6161504
  have htrace : WordTrace (prefixWord ++ tailWord_6161504) baseStart_6161504 baseEnd_6161504 := by
    simpa [prefixWord, tailWord_6161504, baseEnd_6161504] using wordTrace_append hprefix tailTrace_6161504
  have hstable : (prefixWord ++ tailWord_6161504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161504).length < 2 ^ (prefixWord ++ tailWord_6161504).sum := by decide
  have hdescent : baseEnd_6161504 < baseStart_6161504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161512 : List Nat := [2, 1, 4, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6161512 : Nat := 118140960795 + 6161512 * 2 ^ 59
def prefixEnd_6161512 : Nat := 4983230072969 + 3 ^ 40 * 6161512 * 2
def baseEnd_6161512 : Nat := 3163817214445602289663729

theorem tailTrace_6161512 : CollatzResearch.WordTrace tailWord_6161512 prefixEnd_6161512 3163817214445602289663729 := by
  unfold tailWord_6161512
  simp only [CollatzResearch.WordTrace]
  refine ⟨112364402426950900658315395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149819203235934534211087193 112364402426950900658315395)
  ·
    refine ⟨168546603640426350987473093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112364402426950900658315395 168546603640426350987473093)
    ·
      refine ⟨31602488182579940810151205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168546603640426350987473093 31602488182579940810151205)
      ·
        refine ⟨5925466534233738901903351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31602488182579940810151205 5925466534233738901903351)
        ·
          refine ⟨8888199801350608352855027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5925466534233738901903351 8888199801350608352855027)
          ·
            refine ⟨13332299702025912529282541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8888199801350608352855027 13332299702025912529282541)
            ·
              refine ⟨4999612388259717198480953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13332299702025912529282541 4999612388259717198480953)
              ·
                refine ⟨3749709291194787898860715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4999612388259717198480953 3749709291194787898860715)
                ·
                  refine ⟨5624563936792181848291073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3749709291194787898860715 5624563936792181848291073)
                  ·
                    refine ⟨4218422952594136386218305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5624563936792181848291073 4218422952594136386218305)
                    ·
                      refine ⟨3163817214445602289663729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4218422952594136386218305 3163817214445602289663729)
                      ·
                        rfl

theorem cell23_6161512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6161512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161512 prefixEnd_6161512 := by exact prefixLift 6161512
  have htrace : WordTrace (prefixWord ++ tailWord_6161512) baseStart_6161512 baseEnd_6161512 := by
    simpa [prefixWord, tailWord_6161512, baseEnd_6161512] using wordTrace_append hprefix tailTrace_6161512
  have hstable : (prefixWord ++ tailWord_6161512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161512).length < 2 ^ (prefixWord ++ tailWord_6161512).sum := by decide
  have hdescent : baseEnd_6161512 < baseStart_6161512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161520 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 5]
def baseStart_6161520 : Nat := 118140960795 + 6161520 * 2 ^ 59
def prefixEnd_6161520 : Nat := 4983230072969 + 3 ^ 40 * 6161520 * 2
def baseEnd_6161520 : Nat := 3163821322290838258363691

theorem tailTrace_6161520 : CollatzResearch.WordTrace tailWord_6161520 prefixEnd_6161520 3163821322290838258363691 := by
  unfold tailWord_6161520
  simp only [CollatzResearch.WordTrace]
  refine ⟨112364548318936409341461007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149819397758581879121948009 112364548318936409341461007)
  ·
    refine ⟨168546822478404614012191511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112364548318936409341461007 168546822478404614012191511)
    ·
      refine ⟨252820233717606921018287267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168546822478404614012191511 252820233717606921018287267)
      ·
        refine ⟨379230350576410381527430901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252820233717606921018287267 379230350576410381527430901)
        ·
          refine ⟨35552845366538473268196647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 379230350576410381527430901 35552845366538473268196647)
          ·
            refine ⟨53329268049807709902294971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35552845366538473268196647 53329268049807709902294971)
            ·
              refine ⟨79993902074711564853442457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53329268049807709902294971 79993902074711564853442457)
              ·
                refine ⟨59995426556033673640081843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79993902074711564853442457 59995426556033673640081843)
                ·
                  refine ⟨89993139834050510460122765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59995426556033673640081843 89993139834050510460122765)
                  ·
                    refine ⟨33747427437768941422546037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89993139834050510460122765 33747427437768941422546037)
                    ·
                      refine ⟨3163821322290838258363691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33747427437768941422546037 3163821322290838258363691)
                      ·
                        rfl

theorem cell23_6161520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_6161520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161520 prefixEnd_6161520 := by exact prefixLift 6161520
  have htrace : WordTrace (prefixWord ++ tailWord_6161520) baseStart_6161520 baseEnd_6161520 := by
    simpa [prefixWord, tailWord_6161520, baseEnd_6161520] using wordTrace_append hprefix tailTrace_6161520
  have hstable : (prefixWord ++ tailWord_6161520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161520).length < 2 ^ (prefixWord ++ tailWord_6161520).sum := by decide
  have hdescent : baseEnd_6161520 < baseStart_6161520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161537 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_6161537 : Nat := 118140960795 + 6161537 * 2 ^ 59
def prefixEnd_6161537 : Nat := 4983230072969 + 3 ^ 40 * 6161537 * 2
def baseEnd_6161537 : Nat := 3163830051461964691851113

theorem tailTrace_6161537 : CollatzResearch.WordTrace tailWord_6161537 prefixEnd_6161537 3163830051461964691851113 := by
  unfold tailWord_6161537
  simp only [CollatzResearch.WordTrace]
  refine ⟨224729716678811230586290865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149819811119207487057527243 224729716678811230586290865)
  ·
    refine ⟨168547287509108422939718149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224729716678811230586290865 168547287509108422939718149)
    ·
      refine ⟨31602616407957829301197153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168547287509108422939718149 31602616407957829301197153)
      ·
        refine ⟨23701962305968371975897865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31602616407957829301197153 23701962305968371975897865)
        ·
          refine ⟨17776471729476278981923399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23701962305968371975897865 17776471729476278981923399)
          ·
            refine ⟨26664707594214418472885099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17776471729476278981923399 26664707594214418472885099)
            ·
              refine ⟨39997061391321627709327649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26664707594214418472885099 39997061391321627709327649)
              ·
                refine ⟨29997796043491220781995737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39997061391321627709327649 29997796043491220781995737)
                ·
                  refine ⟨22498347032618415586496803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29997796043491220781995737 22498347032618415586496803)
                  ·
                    refine ⟨33747520548927623379745205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22498347032618415586496803 33747520548927623379745205)
                    ·
                      refine ⟨3163830051461964691851113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33747520548927623379745205 3163830051461964691851113)
                      ·
                        rfl

theorem cell23_6161537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_6161537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161537 prefixEnd_6161537 := by exact prefixLift 6161537
  have htrace : WordTrace (prefixWord ++ tailWord_6161537) baseStart_6161537 baseEnd_6161537 := by
    simpa [prefixWord, tailWord_6161537, baseEnd_6161537] using wordTrace_append hprefix tailTrace_6161537
  have hstable : (prefixWord ++ tailWord_6161537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161537).length < 2 ^ (prefixWord ++ tailWord_6161537).sum := by decide
  have hdescent : baseEnd_6161537 < baseStart_6161537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161580 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_6161580 : Nat := 118140960795 + 6161580 * 2 ^ 59
def prefixEnd_6161580 : Nat := 4983230072969 + 3 ^ 40 * 6161580 * 2
def baseEnd_6161580 : Nat := 3163852131130108023613415

theorem tailTrace_6161580 : CollatzResearch.WordTrace tailWord_6161580 prefixEnd_6161580 3163852131130108023613415 := by
  unfold tailWord_6161580
  simp only [CollatzResearch.WordTrace]
  refine ⟨112365642508827724465053097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149820856678436965953404129 112365642508827724465053097)
  ·
    refine ⟨84274231881620793348789823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112365642508827724465053097 84274231881620793348789823)
    ·
      refine ⟨126411347822431190023184735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84274231881620793348789823 126411347822431190023184735)
      ·
        refine ⟨189617021733646785034777103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126411347822431190023184735 189617021733646785034777103)
        ·
          refine ⟨284425532600470177552165655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189617021733646785034777103 284425532600470177552165655)
          ·
            refine ⟨426638298900705266328248483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284425532600470177552165655 426638298900705266328248483)
            ·
              refine ⟨639957448351057899492372725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426638298900705266328248483 639957448351057899492372725)
              ·
                refine ⟨59996010782911678077409943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 639957448351057899492372725 59996010782911678077409943)
                ·
                  refine ⟨89994016174367517116114915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59996010782911678077409943 89994016174367517116114915)
                  ·
                    refine ⟨134991024261551275674172373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89994016174367517116114915 134991024261551275674172373)
                    ·
                      refine ⟨3163852131130108023613415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134991024261551275674172373 3163852131130108023613415)
                      ·
                        rfl

theorem cell23_6161580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_6161580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161580 prefixEnd_6161580 := by exact prefixLift 6161580
  have htrace : WordTrace (prefixWord ++ tailWord_6161580) baseStart_6161580 baseEnd_6161580 := by
    simpa [prefixWord, tailWord_6161580, baseEnd_6161580] using wordTrace_append hprefix tailTrace_6161580
  have hstable : (prefixWord ++ tailWord_6161580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161580).length < 2 ^ (prefixWord ++ tailWord_6161580).sum := by decide
  have hdescent : baseEnd_6161580 < baseStart_6161580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161604 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_6161604 : Nat := 118140960795 + 6161604 * 2 ^ 59
def prefixEnd_6161604 : Nat := 4983230072969 + 3 ^ 40 * 6161604 * 2
def baseEnd_6161604 : Nat := 1054621484888605309904435

theorem tailTrace_6161604 : CollatzResearch.WordTrace tailWord_6161604 prefixEnd_6161604 1054621484888605309904435 := by
  unfold tailWord_6161604
  simp only [CollatzResearch.WordTrace]
  refine ⟨112366080184784250514489933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149821440246379000685986577 112366080184784250514489933)
  ·
    refine ⟨42137280069294093942933725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112366080184784250514489933 42137280069294093942933725)
    ·
      refine ⟨15801480025985285228600147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42137280069294093942933725 15801480025985285228600147)
      ·
        refine ⟨23702220038977927842900221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15801480025985285228600147 23702220038977927842900221)
        ·
          refine ⟨8888332514616722941087583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23702220038977927842900221 8888332514616722941087583)
          ·
            refine ⟨13332498771925084411631375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8888332514616722941087583 13332498771925084411631375)
            ·
              refine ⟨19998748157887626617447063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13332498771925084411631375 19998748157887626617447063)
              ·
                refine ⟨29998122236831439926170595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19998748157887626617447063 29998122236831439926170595)
                ·
                  refine ⟨44997183355247159889255893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29998122236831439926170595 44997183355247159889255893)
                  ·
                    refine ⟨1054621484888605309904435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44997183355247159889255893 1054621484888605309904435)
                    ·
                      rfl

theorem cell23_6161604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_6161604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161604 prefixEnd_6161604 := by exact prefixLift 6161604
  have htrace : WordTrace (prefixWord ++ tailWord_6161604) baseStart_6161604 baseEnd_6161604 := by
    simpa [prefixWord, tailWord_6161604, baseEnd_6161604] using wordTrace_append hprefix tailTrace_6161604
  have hstable : (prefixWord ++ tailWord_6161604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161604).length < 2 ^ (prefixWord ++ tailWord_6161604).sum := by decide
  have hdescent : baseEnd_6161604 < baseStart_6161604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161606 : List Nat := [6, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_6161606 : Nat := 118140960795 + 6161606 * 2 ^ 59
def prefixEnd_6161606 : Nat := 4983230072969 + 3 ^ 40 * 6161606 * 2
def baseEnd_6161606 : Nat := 3163865481627124921888297

theorem tailTrace_6161606 : CollatzResearch.WordTrace tailWord_6161606 prefixEnd_6161606 3163865481627124921888297 := by
  unfold tailWord_6161606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7022882291111289230329771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149821488877040836913701781 7022882291111289230329771)
  ·
    refine ⟨10534323436666933845494657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7022882291111289230329771 10534323436666933845494657)
    ·
      refine ⟨7900742577500200384120993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10534323436666933845494657 7900742577500200384120993)
      ·
        refine ⟨5925556933125150288090745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7900742577500200384120993 5925556933125150288090745)
        ·
          refine ⟨4444167699843862716068059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5925556933125150288090745 4444167699843862716068059)
          ·
            refine ⟨6666251549765794074102089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4444167699843862716068059 6666251549765794074102089)
            ·
              refine ⟨4999688662324345555576567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6666251549765794074102089 4999688662324345555576567)
              ·
                refine ⟨7499532993486518333364851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4999688662324345555576567 7499532993486518333364851)
                ·
                  refine ⟨11249299490229777500047277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7499532993486518333364851 11249299490229777500047277)
                  ·
                    refine ⟨4218487308836166562517729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11249299490229777500047277 4218487308836166562517729)
                    ·
                      refine ⟨3163865481627124921888297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4218487308836166562517729 3163865481627124921888297)
                      ·
                        rfl

theorem cell23_6161606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_6161606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161606 prefixEnd_6161606 := by exact prefixLift 6161606
  have htrace : WordTrace (prefixWord ++ tailWord_6161606) baseStart_6161606 baseEnd_6161606 := by
    simpa [prefixWord, tailWord_6161606, baseEnd_6161606] using wordTrace_append hprefix tailTrace_6161606
  have hstable : (prefixWord ++ tailWord_6161606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161606).length < 2 ^ (prefixWord ++ tailWord_6161606).sum := by decide
  have hdescent : baseEnd_6161606 < baseStart_6161606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161617 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 7, 4]
def baseStart_6161617 : Nat := 118140960795 + 6161617 * 2 ^ 59
def prefixEnd_6161617 : Nat := 4983230072969 + 3 ^ 40 * 6161617 * 2
def baseEnd_6161617 : Nat := 1054623709971441459616915

theorem tailTrace_6161617 : CollatzResearch.WordTrace tailWord_6161617 prefixEnd_6161617 1054623709971441459616915 := by
  unfold tailWord_6161617
  simp only [CollatzResearch.WordTrace]
  refine ⟨224732634518521404249203105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149821756345680936166135403 224732634518521404249203105)
  ·
    refine ⟨168549475888891053186902329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224732634518521404249203105 168549475888891053186902329)
    ·
      refine ⟨126412106916668289890176747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168549475888891053186902329 126412106916668289890176747)
      ·
        refine ⟨189618160375002434835265121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126412106916668289890176747 189618160375002434835265121)
        ·
          refine ⟨142213620281251826126448841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189618160375002434835265121 142213620281251826126448841)
          ·
            refine ⟨106660215210938869594836631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142213620281251826126448841 106660215210938869594836631)
            ·
              refine ⟨159990322816408304392254947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106660215210938869594836631 159990322816408304392254947)
              ·
                refine ⟨239985484224612456588382421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159990322816408304392254947 239985484224612456588382421)
                ·
                  refine ⟨5624659786514354451290213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 239985484224612456588382421 5624659786514354451290213)
                  ·
                    refine ⟨1054623709971441459616915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5624659786514354451290213 1054623709971441459616915)
                    ·
                      rfl

theorem cell23_6161617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_6161617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161617 prefixEnd_6161617 := by exact prefixLift 6161617
  have htrace : WordTrace (prefixWord ++ tailWord_6161617) baseStart_6161617 baseEnd_6161617 := by
    simpa [prefixWord, tailWord_6161617, baseEnd_6161617] using wordTrace_append hprefix tailTrace_6161617
  have hstable : (prefixWord ++ tailWord_6161617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161617).length < 2 ^ (prefixWord ++ tailWord_6161617).sum := by decide
  have hdescent : baseEnd_6161617 < baseStart_6161617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161657 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 2, 5, 3]
def baseStart_6161657 : Nat := 118140960795 + 6161657 * 2 ^ 59
def prefixEnd_6161657 : Nat := 4983230072969 + 3 ^ 40 * 6161657 * 2
def baseEnd_6161657 : Nat := 3163891669140504222350561

theorem tailTrace_6161657 : CollatzResearch.WordTrace tailWord_6161657 prefixEnd_6161657 3163891669140504222350561 := by
  unfold tailWord_6161657
  simp only [CollatzResearch.WordTrace]
  refine ⟨224734093438376491080659225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149822728958917660720439483 224734093438376491080659225)
  ·
    refine ⟨168550570078782368310494419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224734093438376491080659225 168550570078782368310494419)
    ·
      refine ⟨252825855118173552465741629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168550570078782368310494419 252825855118173552465741629)
      ·
        refine ⟨94809695669315082174653111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252825855118173552465741629 94809695669315082174653111)
        ·
          refine ⟨142214543503972623261979667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94809695669315082174653111 142214543503972623261979667)
          ·
            refine ⟨213321815255958934892969501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142214543503972623261979667 213321815255958934892969501)
            ·
              refine ⟨79995680720984600584863563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213321815255958934892969501 79995680720984600584863563)
              ·
                refine ⟨119993521081476900877295345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79995680720984600584863563 119993521081476900877295345)
                ·
                  refine ⟨89995140811107675657971509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119993521081476900877295345 89995140811107675657971509)
                  ·
                    refine ⟨8437044451041344592934829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89995140811107675657971509 8437044451041344592934829)
                    ·
                      refine ⟨3163891669140504222350561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8437044451041344592934829 3163891669140504222350561)
                      ·
                        rfl

theorem cell23_6161657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_6161657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161657 prefixEnd_6161657 := by exact prefixLift 6161657
  have htrace : WordTrace (prefixWord ++ tailWord_6161657) baseStart_6161657 baseEnd_6161657 := by
    simpa [prefixWord, tailWord_6161657, baseEnd_6161657] using wordTrace_append hprefix tailTrace_6161657
  have hstable : (prefixWord ++ tailWord_6161657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161657).length < 2 ^ (prefixWord ++ tailWord_6161657).sum := by decide
  have hdescent : baseEnd_6161657 < baseStart_6161657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161668 : List Nat := [2, 3, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_6161668 : Nat := 118140960795 + 6161668 * 2 ^ 59
def prefixEnd_6161668 : Nat := 4983230072969 + 3 ^ 40 * 6161668 * 2
def baseEnd_6161668 : Nat := 1054632439142567893104337

theorem tailTrace_6161668 : CollatzResearch.WordTrace tailWord_6161668 prefixEnd_6161668 1054632439142567893104337 := by
  unfold tailWord_6161668
  simp only [CollatzResearch.WordTrace]
  refine ⟨112367247320668319979654829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149822996427557759972873105 112367247320668319979654829)
  ·
    refine ⟨42137717745250619992370561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112367247320668319979654829 42137717745250619992370561)
    ·
      refine ⟨31603288308937964994277921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42137717745250619992370561 31603288308937964994277921)
      ·
        refine ⟨23702466231703473745708441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31603288308937964994277921 23702466231703473745708441)
        ·
          refine ⟨17776849673777605309281331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23702466231703473745708441 17776849673777605309281331)
          ·
            refine ⟨26665274510666407963921997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17776849673777605309281331 26665274510666407963921997)
            ·
              refine ⟨9999477941499902986470749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26665274510666407963921997 9999477941499902986470749)
              ·
                refine ⟨3749804228062463619926531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9999477941499902986470749 3749804228062463619926531)
                ·
                  refine ⟨5624706342093695429889797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3749804228062463619926531 5624706342093695429889797)
                  ·
                    refine ⟨1054632439142567893104337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5624706342093695429889797 1054632439142567893104337)
                    ·
                      rfl

theorem cell23_6161668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_6161668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161668 prefixEnd_6161668 := by exact prefixLift 6161668
  have htrace : WordTrace (prefixWord ++ tailWord_6161668) baseStart_6161668 baseEnd_6161668 := by
    simpa [prefixWord, tailWord_6161668, baseEnd_6161668] using wordTrace_append hprefix tailTrace_6161668
  have hstable : (prefixWord ++ tailWord_6161668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161668).length < 2 ^ (prefixWord ++ tailWord_6161668).sum := by decide
  have hdescent : baseEnd_6161668 < baseStart_6161668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161697 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_6161697 : Nat := 118140960795 + 6161697 * 2 ^ 59
def prefixEnd_6161697 : Nat := 4983230072969 + 3 ^ 40 * 6161697 * 2
def baseEnd_6161697 : Nat := 3163912208366684065850377

theorem tailTrace_6161697 : CollatzResearch.WordTrace tailWord_6161697 prefixEnd_6161697 3163912208366684065850377 := by
  unfold tailWord_6161697
  simp only [CollatzResearch.WordTrace]
  refine ⟨224735552358231577912115345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149823701572154385274743563 224735552358231577912115345)
  ·
    refine ⟨168551664268673683434086509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224735552358231577912115345 168551664268673683434086509)
    ·
      refine ⟨63206874100752631287782441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168551664268673683434086509 63206874100752631287782441)
      ·
        refine ⟨47405155575564473465836831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63206874100752631287782441 47405155575564473465836831)
        ·
          refine ⟨71107733363346710198755247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47405155575564473465836831 71107733363346710198755247)
          ·
            refine ⟨106661600045020065298132871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71107733363346710198755247 106661600045020065298132871)
            ·
              refine ⟨159992400067530097947199307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106661600045020065298132871 159992400067530097947199307)
              ·
                refine ⟨239988600101295146920798961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159992400067530097947199307 239988600101295146920798961)
                ·
                  refine ⟨179991450075971360190599221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239988600101295146920798961 179991450075971360190599221)
                  ·
                    refine ⟨16874198444622315017868677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 179991450075971360190599221 16874198444622315017868677)
                    ·
                      refine ⟨3163912208366684065850377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16874198444622315017868677 3163912208366684065850377)
                      ·
                        rfl

theorem cell23_6161697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_6161697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161697 prefixEnd_6161697 := by exact prefixLift 6161697
  have htrace : WordTrace (prefixWord ++ tailWord_6161697) baseStart_6161697 baseEnd_6161697 := by
    simpa [prefixWord, tailWord_6161697, baseEnd_6161697] using wordTrace_append hprefix tailTrace_6161697
  have hstable : (prefixWord ++ tailWord_6161697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161697).length < 2 ^ (prefixWord ++ tailWord_6161697).sum := by decide
  have hdescent : baseEnd_6161697 < baseStart_6161697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161698 : List Nat := [3, 3, 1, 1, 4, 2, 2, 1, 6]
def baseStart_6161698 : Nat := 118140960795 + 6161698 * 2 ^ 59
def prefixEnd_6161698 : Nat := 4983230072969 + 3 ^ 40 * 6161698 * 2
def baseEnd_6161698 : Nat := 351545857983037617993097

theorem tailTrace_6161698 : CollatzResearch.WordTrace tailWord_6161698 prefixEnd_6161698 351545857983037617993097 := by
  unfold tailWord_6161698
  simp only [CollatzResearch.WordTrace]
  refine ⟨56183897207806988770725437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149823725887485303388601165 56183897207806988770725437)
  ·
    refine ⟨21068961452927620789022039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56183897207806988770725437 21068961452927620789022039)
    ·
      refine ⟨31603442179391431183533059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21068961452927620789022039 31603442179391431183533059)
      ·
        refine ⟨47405163269087146775299589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31603442179391431183533059 47405163269087146775299589)
        ·
          refine ⟨8888468112953840020368673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47405163269087146775299589 8888468112953840020368673)
          ·
            refine ⟨6666351084715380015276505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8888468112953840020368673 6666351084715380015276505)
            ·
              refine ⟨4999763313536535011457379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6666351084715380015276505 4999763313536535011457379)
              ·
                refine ⟨7499644970304802517186069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4999763313536535011457379 7499644970304802517186069)
                ·
                  refine ⟨351545857983037617993097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7499644970304802517186069 351545857983037617993097)
                  ·
                    rfl

theorem cell23_6161698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_6161698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161698 prefixEnd_6161698 := by exact prefixLift 6161698
  have htrace : WordTrace (prefixWord ++ tailWord_6161698) baseStart_6161698 baseEnd_6161698 := by
    simpa [prefixWord, tailWord_6161698, baseEnd_6161698] using wordTrace_append hprefix tailTrace_6161698
  have hstable : (prefixWord ++ tailWord_6161698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161698).length < 2 ^ (prefixWord ++ tailWord_6161698).sum := by decide
  have hdescent : baseEnd_6161698 < baseStart_6161698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161724 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 1, 6]
def baseStart_6161724 : Nat := 118140960795 + 6161724 * 2 ^ 59
def prefixEnd_6161724 : Nat := 4983230072969 + 3 ^ 40 * 6161724 * 2
def baseEnd_6161724 : Nat := 1054642024114785153404251

theorem tailTrace_6161724 : CollatzResearch.WordTrace tailWord_6161724 prefixEnd_6161724 1054642024114785153404251 := by
  unfold tailWord_6161724
  simp only [CollatzResearch.WordTrace]
  refine ⟨112368268564566880761674113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149824358086089174348898817 112368268564566880761674113)
  ·
    refine ⟨84276201423425160571255585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112368268564566880761674113 84276201423425160571255585)
    ·
      refine ⟨63207151067568870428441689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84276201423425160571255585 63207151067568870428441689)
      ·
        refine ⟨47405363300676652821331267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63207151067568870428441689 47405363300676652821331267)
        ·
          refine ⟨71108044951014979231996901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47405363300676652821331267 71108044951014979231996901)
          ·
            refine ⟨13332758428315308605999419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71108044951014979231996901 13332758428315308605999419)
            ·
              refine ⟨19999137642472962908999129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13332758428315308605999419 19999137642472962908999129)
              ·
                refine ⟨14999353231854722181749347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19999137642472962908999129 14999353231854722181749347)
                ·
                  refine ⟨22499029847782083272624021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14999353231854722181749347 22499029847782083272624021)
                  ·
                    refine ⟨1054642024114785153404251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22499029847782083272624021 1054642024114785153404251)
                    ·
                      rfl

theorem cell23_6161724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_6161724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161724 prefixEnd_6161724 := by exact prefixLift 6161724
  have htrace : WordTrace (prefixWord ++ tailWord_6161724) baseStart_6161724 baseEnd_6161724 := by
    simpa [prefixWord, tailWord_6161724, baseEnd_6161724] using wordTrace_append hprefix tailTrace_6161724
  have hstable : (prefixWord ++ tailWord_6161724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161724).length < 2 ^ (prefixWord ++ tailWord_6161724).sum := by decide
  have hdescent : baseEnd_6161724 < baseStart_6161724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161748 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_6161748 : Nat := 118140960795 + 6161748 * 2 ^ 59
def prefixEnd_6161748 : Nat := 4983230072969 + 3 ^ 40 * 6161748 * 2
def baseEnd_6161748 : Nat := 3163938395880063366312643

theorem tailTrace_6161748 : CollatzResearch.WordTrace tailWord_6161748 prefixEnd_6161748 3163938395880063366312643 := by
  unfold tailWord_6161748
  simp only [CollatzResearch.WordTrace]
  refine ⟨112368706240523406811110949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149824941654031209081481265 112368706240523406811110949)
  ·
    refine ⟨21069132420098138777083303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112368706240523406811110949 21069132420098138777083303)
    ·
      refine ⟨31603698630147208165624955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21069132420098138777083303 31603698630147208165624955)
      ·
        refine ⟨47405547945220812248437433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31603698630147208165624955 47405547945220812248437433)
        ·
          refine ⟨35554160958915609186328075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47405547945220812248437433 35554160958915609186328075)
          ·
            refine ⟨53331241438373413779492113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35554160958915609186328075 53331241438373413779492113)
            ·
              refine ⟨39998431078780060334619085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53331241438373413779492113 39998431078780060334619085)
              ·
                refine ⟨14999411654542522625482157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39998431078780060334619085 14999411654542522625482157)
                ·
                  refine ⟨5624779370453445984555809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14999411654542522625482157 5624779370453445984555809)
                  ·
                    refine ⟨4218584527840084488416857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5624779370453445984555809 4218584527840084488416857)
                    ·
                      refine ⟨3163938395880063366312643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4218584527840084488416857 3163938395880063366312643)
                      ·
                        rfl

theorem cell23_6161748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_6161748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161748 prefixEnd_6161748 := by exact prefixLift 6161748
  have htrace : WordTrace (prefixWord ++ tailWord_6161748) baseStart_6161748 baseEnd_6161748 := by
    simpa [prefixWord, tailWord_6161748, baseEnd_6161748] using wordTrace_append hprefix tailTrace_6161748
  have hstable : (prefixWord ++ tailWord_6161748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161748).length < 2 ^ (prefixWord ++ tailWord_6161748).sum := by decide
  have hdescent : baseEnd_6161748 < baseStart_6161748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161824 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 5]
def baseStart_6161824 : Nat := 118140960795 + 6161824 * 2 ^ 59
def prefixEnd_6161824 : Nat := 4983230072969 + 3 ^ 40 * 6161824 * 2
def baseEnd_6161824 : Nat := 3163977420409805068962293

theorem tailTrace_6161824 : CollatzResearch.WordTrace tailWord_6161824 prefixEnd_6161824 3163977420409805068962293 := by
  unfold tailWord_6161824
  simp only [CollatzResearch.WordTrace]
  refine ⟨112370092214385739300994263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149826789619180985734659017 112370092214385739300994263)
  ·
    refine ⟨168555138321578608951491395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112370092214385739300994263 168555138321578608951491395)
    ·
      refine ⟨252832707482367913427237093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168555138321578608951491395 252832707482367913427237093)
      ·
        refine ⟨47406132652943983767606955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252832707482367913427237093 47406132652943983767606955)
        ·
          refine ⟨71109198979415975651410433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47406132652943983767606955 71109198979415975651410433)
          ·
            refine ⟨53331899234561981738557825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71109198979415975651410433 53331899234561981738557825)
            ·
              refine ⟨39998924425921486303918369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53331899234561981738557825 39998924425921486303918369)
              ·
                refine ⟨29999193319441114727938777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39998924425921486303918369 29999193319441114727938777)
                ·
                  refine ⟨22499394989580836045954083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29999193319441114727938777 22499394989580836045954083)
                  ·
                    refine ⟨33749092484371254068931125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22499394989580836045954083 33749092484371254068931125)
                    ·
                      refine ⟨3163977420409805068962293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33749092484371254068931125 3163977420409805068962293)
                      ·
                        rfl

theorem cell23_6161824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_6161824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161824 prefixEnd_6161824 := by exact prefixLift 6161824
  have htrace : WordTrace (prefixWord ++ tailWord_6161824) baseStart_6161824 baseEnd_6161824 := by
    simpa [prefixWord, tailWord_6161824, baseEnd_6161824] using wordTrace_append hprefix tailTrace_6161824
  have hstable : (prefixWord ++ tailWord_6161824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161824).length < 2 ^ (prefixWord ++ tailWord_6161824).sum := by decide
  have hdescent : baseEnd_6161824 < baseStart_6161824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161854 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_6161854 : Nat := 118140960795 + 6161854 * 2 ^ 59
def prefixEnd_6161854 : Nat := 4983230072969 + 3 ^ 40 * 6161854 * 2
def baseEnd_6161854 : Nat := 3163992824829439951587155

theorem tailTrace_6161854 : CollatzResearch.WordTrace tailWord_6161854 prefixEnd_6161854 3163992824829439951587155 := by
  unfold tailWord_6161854
  simp only [CollatzResearch.WordTrace]
  refine ⟨28092659827332849215697577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149827519079108529150387077 28092659827332849215697577)
  ·
    refine ⟨21069494870499636911773183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28092659827332849215697577 21069494870499636911773183)
    ·
      refine ⟨31604242305749455367659775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21069494870499636911773183 31604242305749455367659775)
      ·
        refine ⟨47406363458624183051489663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31604242305749455367659775 47406363458624183051489663)
        ·
          refine ⟨71109545187936274577234495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47406363458624183051489663 71109545187936274577234495)
          ·
            refine ⟨106664317781904411865851743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71109545187936274577234495 106664317781904411865851743)
            ·
              refine ⟨159996476672856617798777615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106664317781904411865851743 159996476672856617798777615)
              ·
                refine ⟨239994715009284926698166423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159996476672856617798777615 239994715009284926698166423)
                ·
                  refine ⟨359992072513927390047249635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239994715009284926698166423 359992072513927390047249635)
                  ·
                    refine ⟨539988108770891085070874453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 359992072513927390047249635 539988108770891085070874453)
                    ·
                      refine ⟨3163992824829439951587155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 539988108770891085070874453 3163992824829439951587155)
                      ·
                        rfl

theorem cell23_6161854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_6161854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161854 prefixEnd_6161854 := by exact prefixLift 6161854
  have htrace : WordTrace (prefixWord ++ tailWord_6161854) baseStart_6161854 baseEnd_6161854 := by
    simpa [prefixWord, tailWord_6161854, baseEnd_6161854] using wordTrace_append hprefix tailTrace_6161854
  have hstable : (prefixWord ++ tailWord_6161854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161854).length < 2 ^ (prefixWord ++ tailWord_6161854).sum := by decide
  have hdescent : baseEnd_6161854 < baseStart_6161854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161891 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 2, 5]
def baseStart_6161891 : Nat := 118140960795 + 6161891 * 2 ^ 59
def prefixEnd_6161891 : Nat := 4983230072969 + 3 ^ 40 * 6161891 * 2
def baseEnd_6161891 : Nat := 1054670607871218768941495

theorem tailTrace_6161891 : CollatzResearch.WordTrace tailWord_6161891 prefixEnd_6161891 1054670607871218768941495 := by
  unfold tailWord_6161891
  simp only [CollatzResearch.WordTrace]
  refine ⟨224742628119528749044677527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149828418746352499363118351 224742628119528749044677527)
  ·
    refine ⟨337113942179293123567016291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224742628119528749044677527 337113942179293123567016291)
    ·
      refine ⟨505670913268939685350524437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337113942179293123567016291 505670913268939685350524437)
      ·
        refine ⟨23703324059481547750805833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 505670913268939685350524437 23703324059481547750805833)
        ·
          refine ⟨17777493044611160813104375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23703324059481547750805833 17777493044611160813104375)
          ·
            refine ⟨26666239566916741219656563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17777493044611160813104375 26666239566916741219656563)
            ·
              refine ⟨39999359350375111829484845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26666239566916741219656563 39999359350375111829484845)
              ·
                refine ⟨14999759756390666936056817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39999359350375111829484845 14999759756390666936056817)
                ·
                  refine ⟨11249819817293000202042613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14999759756390666936056817 11249819817293000202042613)
                  ·
                    refine ⟨1054670607871218768941495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11249819817293000202042613 1054670607871218768941495)
                    ·
                      rfl

theorem cell23_6161891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 5].length) (baseStart_6161891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161891 prefixEnd_6161891 := by exact prefixLift 6161891
  have htrace : WordTrace (prefixWord ++ tailWord_6161891) baseStart_6161891 baseEnd_6161891 := by
    simpa [prefixWord, tailWord_6161891, baseEnd_6161891] using wordTrace_append hprefix tailTrace_6161891
  have hstable : (prefixWord ++ tailWord_6161891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161891).length < 2 ^ (prefixWord ++ tailWord_6161891).sum := by decide
  have hdescent : baseEnd_6161891 < baseStart_6161891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6161914 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_6161914 : Nat := 118140960795 + 6161914 * 2 ^ 59
def prefixEnd_6161914 : Nat := 4983230072969 + 3 ^ 40 * 6161914 * 2
def baseEnd_6161914 : Nat := 3164023633668709716836879

theorem tailTrace_6161914 : CollatzResearch.WordTrace tailWord_6161914 prefixEnd_6161914 3164023633668709716836879 := by
  unfold tailWord_6161914
  simp only [CollatzResearch.WordTrace]
  refine ⟨56185866749611355993191199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149828977998963615981843197 56185866749611355993191199)
  ·
    refine ⟨84278800124417033989786799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56185866749611355993191199 84278800124417033989786799)
    ·
      refine ⟨126418200186625550984680199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84278800124417033989786799 126418200186625550984680199)
      ·
        refine ⟨189627300279938326477020299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126418200186625550984680199 189627300279938326477020299)
        ·
          refine ⟨284440950419907489715530449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189627300279938326477020299 284440950419907489715530449)
          ·
            refine ⟨213330712814930617286647837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284440950419907489715530449 213330712814930617286647837)
            ·
              refine ⟨79999017305598981482492939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213330712814930617286647837 79999017305598981482492939)
              ·
                refine ⟨119998525958398472223739409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79999017305598981482492939 119998525958398472223739409)
                ·
                  refine ⟨89998894468798854167804557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119998525958398472223739409 89998894468798854167804557)
                  ·
                    refine ⟨33749585425799570312926709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89998894468798854167804557 33749585425799570312926709)
                    ·
                      refine ⟨3164023633668709716836879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33749585425799570312926709 3164023633668709716836879)
                      ·
                        rfl

theorem cell23_6161914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_6161914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6161914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6161914 prefixEnd_6161914 := by exact prefixLift 6161914
  have htrace : WordTrace (prefixWord ++ tailWord_6161914) baseStart_6161914 baseEnd_6161914 := by
    simpa [prefixWord, tailWord_6161914, baseEnd_6161914] using wordTrace_append hprefix tailTrace_6161914
  have hstable : (prefixWord ++ tailWord_6161914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6161914).length < 2 ^ (prefixWord ++ tailWord_6161914).sum := by decide
  have hdescent : baseEnd_6161914 < baseStart_6161914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6161914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162028 : List Nat := [2, 2, 1, 1, 3, 1, 1, 6, 2, 4]
def baseStart_6162028 : Nat := 118140960795 + 6162028 * 2 ^ 59
def prefixEnd_6162028 : Nat := 4983230072969 + 3 ^ 40 * 6162028 * 2
def baseEnd_6162028 : Nat := 1054694056821107423603785

theorem tailTrace_6162028 : CollatzResearch.WordTrace tailWord_6162028 prefixEnd_6162028 1054694056821107423603785 := by
  unfold tailWord_6162028
  simp only [CollatzResearch.WordTrace]
  refine ⟨112373812460016210721207369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149831749946688280961609825 112373812460016210721207369)
  ·
    refine ⟨84280359345012158040905527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112373812460016210721207369 84280359345012158040905527)
    ·
      refine ⟨126420539017518237061358291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84280359345012158040905527 126420539017518237061358291)
      ·
        refine ⟨189630808526277355592037437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126420539017518237061358291 189630808526277355592037437)
        ·
          refine ⟨71111553197354008347014039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189630808526277355592037437 71111553197354008347014039)
          ·
            refine ⟨106667329796031012520521059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71111553197354008347014039 106667329796031012520521059)
            ·
              refine ⟨160000994694046518780781589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106667329796031012520521059 160000994694046518780781589)
              ·
                refine ⟨7500046626283430567849137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160000994694046518780781589 7500046626283430567849137)
                ·
                  refine ⟨5625034969712572925886853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7500046626283430567849137 5625034969712572925886853)
                  ·
                    refine ⟨1054694056821107423603785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5625034969712572925886853 1054694056821107423603785)
                    ·
                      rfl

theorem cell23_6162028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_6162028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162028 prefixEnd_6162028 := by exact prefixLift 6162028
  have htrace : WordTrace (prefixWord ++ tailWord_6162028) baseStart_6162028 baseEnd_6162028 := by
    simpa [prefixWord, tailWord_6162028, baseEnd_6162028] using wordTrace_append hprefix tailTrace_6162028
  have hstable : (prefixWord ++ tailWord_6162028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162028).length < 2 ^ (prefixWord ++ tailWord_6162028).sum := by decide
  have hdescent : baseEnd_6162028 < baseStart_6162028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162029 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_6162029 : Nat := 118140960795 + 6162029 * 2 ^ 59
def prefixEnd_6162029 : Nat := 4983230072969 + 3 ^ 40 * 6162029 * 2
def baseEnd_6162029 : Nat := 3164082683943976766898851

theorem tailTrace_6162029 : CollatzResearch.WordTrace tailWord_6162029 prefixEnd_6162029 3164082683943976766898851 := by
  unfold tailWord_6162029
  simp only [CollatzResearch.WordTrace]
  refine ⟨224747661393028798613201141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149831774262019199075467427 224747661393028798613201141)
  ·
    refine ⟨21070093255596449869987607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224747661393028798613201141 21070093255596449869987607)
    ·
      refine ⟨31605139883394674804981411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21070093255596449869987607 31605139883394674804981411)
      ·
        refine ⟨47407709825092012207472117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31605139883394674804981411 47407709825092012207472117)
        ·
          refine ⟨4444472796102376144450511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47407709825092012207472117 4444472796102376144450511)
          ·
            refine ⟨6666709194153564216675767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4444472796102376144450511 6666709194153564216675767)
            ·
              refine ⟨10000063791230346325013651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6666709194153564216675767 10000063791230346325013651)
              ·
                refine ⟨15000095686845519487520477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10000063791230346325013651 15000095686845519487520477)
                ·
                  refine ⟨5625035882567069807820179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15000095686845519487520477 5625035882567069807820179)
                  ·
                    refine ⟨8437553823850604711730269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5625035882567069807820179 8437553823850604711730269)
                    ·
                      refine ⟨3164082683943976766898851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8437553823850604711730269 3164082683943976766898851)
                      ·
                        rfl

theorem cell23_6162029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_6162029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162029 prefixEnd_6162029 := by exact prefixLift 6162029
  have htrace : WordTrace (prefixWord ++ tailWord_6162029) baseStart_6162029 baseEnd_6162029 := by
    simpa [prefixWord, tailWord_6162029, baseEnd_6162029] using wordTrace_append hprefix tailTrace_6162029
  have hstable : (prefixWord ++ tailWord_6162029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162029).length < 2 ^ (prefixWord ++ tailWord_6162029).sum := by decide
  have hdescent : baseEnd_6162029 < baseStart_6162029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162041 : List Nat := [1, 2, 1, 3, 3, 1, 4, 8]
def baseStart_6162041 : Nat := 118140960795 + 6162041 * 2 ^ 59
def prefixEnd_6162041 : Nat := 4983230072969 + 3 ^ 40 * 6162041 * 2
def baseEnd_6162041 : Nat := 117188475767104841479585

theorem tailTrace_6162041 : CollatzResearch.WordTrace tailWord_6162041 prefixEnd_6162041 117188475767104841479585 := by
  unfold tailWord_6162041
  simp only [CollatzResearch.WordTrace]
  refine ⟨224748099068985324662637977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149832066045990216441758651 224748099068985324662637977)
  ·
    refine ⟨168561074301738993496978483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224748099068985324662637977 168561074301738993496978483)
    ·
      refine ⟨252841611452608490245467725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168561074301738993496978483 252841611452608490245467725)
      ·
        refine ⟨94815604294728183842050397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252841611452608490245467725 94815604294728183842050397)
        ·
          refine ⟨35555851610523068940768899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94815604294728183842050397 35555851610523068940768899)
          ·
            refine ⟨53333777415784603411153349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35555851610523068940768899 53333777415784603411153349)
            ·
              refine ⟨10000083265459613139591253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53333777415784603411153349 10000083265459613139591253)
              ·
                refine ⟨117188475767104841479585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10000083265459613139591253 117188475767104841479585)
                ·
                  rfl

theorem cell23_6162041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 8].length) (baseStart_6162041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162041 prefixEnd_6162041 := by exact prefixLift 6162041
  have htrace : WordTrace (prefixWord ++ tailWord_6162041) baseStart_6162041 baseEnd_6162041 := by
    simpa [prefixWord, tailWord_6162041, baseEnd_6162041] using wordTrace_append hprefix tailTrace_6162041
  have hstable : (prefixWord ++ tailWord_6162041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162041).length < 2 ^ (prefixWord ++ tailWord_6162041).sum := by decide
  have hdescent : baseEnd_6162041 < baseStart_6162041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162045 : List Nat := [1, 4, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_6162045 : Nat := 118140960795 + 6162045 * 2 ^ 59
def prefixEnd_6162045 : Nat := 4983230072969 + 3 ^ 40 * 6162045 * 2
def baseEnd_6162045 : Nat := 1054696966544816234766259

theorem tailTrace_6162045 : CollatzResearch.WordTrace tailWord_6162045 prefixEnd_6162045 1054696966544816234766259 := by
  unfold tailWord_6162045
  simp only [CollatzResearch.WordTrace]
  refine ⟨224748244960970833345783589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149832163307313888897189059 224748244960970833345783589)
  ·
    refine ⟨42140295930182031252334423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224748244960970833345783589 42140295930182031252334423)
    ·
      refine ⟨63210443895273046878501635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42140295930182031252334423 63210443895273046878501635)
      ·
        refine ⟨94815665842909570317752453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63210443895273046878501635 94815665842909570317752453)
        ·
          refine ⟨17777937345545544434578585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94815665842909570317752453 17777937345545544434578585)
          ·
            refine ⟨13333453009159158325933939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17777937345545544434578585 13333453009159158325933939)
            ·
              refine ⟨20000179513738737488900909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13333453009159158325933939 20000179513738737488900909)
              ·
                refine ⟨7500067317652026558337841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20000179513738737488900909 7500067317652026558337841)
                ·
                  refine ⟨5625050488239019918753381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7500067317652026558337841 5625050488239019918753381)
                  ·
                    refine ⟨1054696966544816234766259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5625050488239019918753381 1054696966544816234766259)
                    ·
                      rfl

theorem cell23_6162045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_6162045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162045 prefixEnd_6162045 := by exact prefixLift 6162045
  have htrace : WordTrace (prefixWord ++ tailWord_6162045) baseStart_6162045 baseEnd_6162045 := by
    simpa [prefixWord, tailWord_6162045, baseEnd_6162045] using wordTrace_append hprefix tailTrace_6162045
  have hstable : (prefixWord ++ tailWord_6162045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162045).length < 2 ^ (prefixWord ++ tailWord_6162045).sum := by decide
  have hdescent : baseEnd_6162045 < baseStart_6162045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162052 : List Nat := [2, 3, 2, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_6162052 : Nat := 118140960795 + 6162052 * 2 ^ 59
def prefixEnd_6162052 : Nat := 4983230072969 + 3 ^ 40 * 6162052 * 2
def baseEnd_6162052 : Nat := 3164094493999030176911245

theorem tailTrace_6162052 : CollatzResearch.WordTrace tailWord_6162052 prefixEnd_6162052 3164094493999030176911245 := by
  unfold tailWord_6162052
  simp only [CollatzResearch.WordTrace]
  refine ⟨112374250135972736770644205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149832333514630315694192273 112374250135972736770644205)
  ·
    refine ⟨42140343800989776288991577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112374250135972736770644205 42140343800989776288991577)
    ·
      refine ⟨31605257850742332216743683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42140343800989776288991577 31605257850742332216743683)
      ·
        refine ⟨47407886776113498325115525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31605257850742332216743683 47407886776113498325115525)
        ·
          refine ⟨8888978770521280935959161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47407886776113498325115525 8888978770521280935959161)
          ·
            refine ⟨6666734077890960701969371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8888978770521280935959161 6666734077890960701969371)
            ·
              refine ⟨10000101116836441052954057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6666734077890960701969371 10000101116836441052954057)
              ·
                refine ⟨7500075837627330789715543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10000101116836441052954057 7500075837627330789715543)
                ·
                  refine ⟨11250113756440996184573315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7500075837627330789715543 11250113756440996184573315)
                  ·
                    refine ⟨16875170634661494276859973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11250113756440996184573315 16875170634661494276859973)
                    ·
                      refine ⟨3164094493999030176911245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16875170634661494276859973 3164094493999030176911245)
                      ·
                        rfl

theorem cell23_6162052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_6162052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162052 prefixEnd_6162052 := by exact prefixLift 6162052
  have htrace : WordTrace (prefixWord ++ tailWord_6162052) baseStart_6162052 baseEnd_6162052 := by
    simpa [prefixWord, tailWord_6162052, baseEnd_6162052] using wordTrace_append hprefix tailTrace_6162052
  have hstable : (prefixWord ++ tailWord_6162052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162052).length < 2 ^ (prefixWord ++ tailWord_6162052).sum := by decide
  have hdescent : baseEnd_6162052 < baseStart_6162052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162055 : List Nat := [1, 1, 4, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_6162055 : Nat := 118140960795 + 6162055 * 2 ^ 59
def prefixEnd_6162055 : Nat := 4983230072969 + 3 ^ 40 * 6162055 * 2
def baseEnd_6162055 : Nat := 3164096034440993665173731

theorem tailTrace_6162055 : CollatzResearch.WordTrace tailWord_6162055 prefixEnd_6162055 3164096034440993665173731 := by
  unfold tailWord_6162055
  simp only [CollatzResearch.WordTrace]
  refine ⟨224748609690934605053647619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149832406460623070035765079 224748609690934605053647619)
  ·
    refine ⟨337122914536401907580471429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224748609690934605053647619 337122914536401907580471429)
    ·
      refine ⟨63210546475575357671338393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337122914536401907580471429 63210546475575357671338393)
      ·
        refine ⟨47407909856681518253503795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63210546475575357671338393 47407909856681518253503795)
        ·
          refine ⟨71111864785022277380255693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47407909856681518253503795 71111864785022277380255693)
          ·
            refine ⟨26666949294383354017595885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71111864785022277380255693 26666949294383354017595885)
            ·
              refine ⟨10000105985393757756598457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26666949294383354017595885 10000105985393757756598457)
              ·
                refine ⟨7500079489045318317448843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10000105985393757756598457 7500079489045318317448843)
                ·
                  refine ⟨11250119233567977476173265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7500079489045318317448843 11250119233567977476173265)
                  ·
                    refine ⟨8437589425175983107129949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11250119233567977476173265 8437589425175983107129949)
                    ·
                      refine ⟨3164096034440993665173731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8437589425175983107129949 3164096034440993665173731)
                      ·
                        rfl

theorem cell23_6162055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_6162055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162055 prefixEnd_6162055 := by exact prefixLift 6162055
  have htrace : WordTrace (prefixWord ++ tailWord_6162055) baseStart_6162055 baseEnd_6162055 := by
    simpa [prefixWord, tailWord_6162055, baseEnd_6162055] using wordTrace_append hprefix tailTrace_6162055
  have hstable : (prefixWord ++ tailWord_6162055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162055).length < 2 ^ (prefixWord ++ tailWord_6162055).sum := by decide
  have hdescent : baseEnd_6162055 < baseStart_6162055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162072 : List Nat := [2, 1, 2, 4, 1, 3, 3, 1, 1, 2, 3]
def baseStart_6162072 : Nat := 118140960795 + 6162072 * 2 ^ 59
def prefixEnd_6162072 : Nat := 4983230072969 + 3 ^ 40 * 6162072 * 2
def baseEnd_6162072 : Nat := 3164104763612120098661153

theorem tailTrace_6162072 : CollatzResearch.WordTrace tailWord_6162072 prefixEnd_6162072 3164104763612120098661153 := by
  unfold tailWord_6162072
  simp only [CollatzResearch.WordTrace]
  refine ⟨112374614865936508478508235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149832819821248677971344313 112374614865936508478508235)
  ·
    refine ⟨168561922298904762717762353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112374614865936508478508235 168561922298904762717762353)
    ·
      refine ⟨126421441724178572038321765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168561922298904762717762353 126421441724178572038321765)
      ·
        refine ⟨23704020323283482257185331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126421441724178572038321765 23704020323283482257185331)
        ·
          refine ⟨35556030484925223385777997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23704020323283482257185331 35556030484925223385777997)
          ·
            refine ⟨13333511431846958769666749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35556030484925223385777997 13333511431846958769666749)
            ·
              refine ⟨5000066786942609538625031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13333511431846958769666749 5000066786942609538625031)
              ·
                refine ⟨7500100180413914307937547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5000066786942609538625031 7500100180413914307937547)
                ·
                  refine ⟨11250150270620871461906321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7500100180413914307937547 11250150270620871461906321)
                  ·
                    refine ⟨8437612702965653596429741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11250150270620871461906321 8437612702965653596429741)
                    ·
                      refine ⟨3164104763612120098661153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8437612702965653596429741 3164104763612120098661153)
                      ·
                        rfl

theorem cell23_6162072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_6162072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162072 prefixEnd_6162072 := by exact prefixLift 6162072
  have htrace : WordTrace (prefixWord ++ tailWord_6162072) baseStart_6162072 baseEnd_6162072 := by
    simpa [prefixWord, tailWord_6162072, baseEnd_6162072] using wordTrace_append hprefix tailTrace_6162072
  have hstable : (prefixWord ++ tailWord_6162072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162072).length < 2 ^ (prefixWord ++ tailWord_6162072).sum := by decide
  have hdescent : baseEnd_6162072 < baseStart_6162072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162085 : List Nat := [1, 3, 1, 2, 1, 2, 3, 4, 2, 1, 3]
def baseStart_6162085 : Nat := 118140960795 + 6162085 * 2 ^ 59
def prefixEnd_6162085 : Nat := 4983230072969 + 3 ^ 40 * 6162085 * 2
def baseEnd_6162085 : Nat := 3164111438860628547798593

theorem tailTrace_6162085 : CollatzResearch.WordTrace tailWord_6162085 prefixEnd_6162085 3164111438860628547798593 := by
  unfold tailWord_6162085
  simp only [CollatzResearch.WordTrace]
  refine ⟨224749703880825920177239709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149833135920550613451493139 224749703880825920177239709)
  ·
    refine ⟨84281138955309720066464891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224749703880825920177239709 84281138955309720066464891)
    ·
      refine ⟨126421708432964580099697337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84281138955309720066464891 126421708432964580099697337)
      ·
        refine ⟨94816281324723435074773003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126421708432964580099697337 94816281324723435074773003)
        ·
          refine ⟨142224421987085152612159505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94816281324723435074773003 142224421987085152612159505)
          ·
            refine ⟨106668316490313864459119629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142224421987085152612159505 106668316490313864459119629)
            ·
              refine ⟨40000618683867699172169861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106668316490313864459119629 40000618683867699172169861)
              ·
                refine ⟨7500116003225193594781849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40000618683867699172169861 7500116003225193594781849)
                ·
                  refine ⟨5625087002418895196086387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7500116003225193594781849 5625087002418895196086387)
                  ·
                    refine ⟨8437630503628342794129581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5625087002418895196086387 8437630503628342794129581)
                    ·
                      refine ⟨3164111438860628547798593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8437630503628342794129581 3164111438860628547798593)
                      ·
                        rfl

theorem cell23_6162085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_6162085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162085 prefixEnd_6162085 := by exact prefixLift 6162085
  have htrace : WordTrace (prefixWord ++ tailWord_6162085) baseStart_6162085 baseEnd_6162085 := by
    simpa [prefixWord, tailWord_6162085, baseEnd_6162085] using wordTrace_append hprefix tailTrace_6162085
  have hstable : (prefixWord ++ tailWord_6162085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162085).length < 2 ^ (prefixWord ++ tailWord_6162085).sum := by decide
  have hdescent : baseEnd_6162085 < baseStart_6162085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162102 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_6162102 : Nat := 118140960795 + 6162102 * 2 ^ 59
def prefixEnd_6162102 : Nat := 4983230072969 + 3 ^ 40 * 6162102 * 2
def baseEnd_6162102 : Nat := 3164120168031754981286015

theorem tailTrace_6162102 : CollatzResearch.WordTrace tailWord_6162102 prefixEnd_6162102 3164120168031754981286015 := by
  unfold tailWord_6162102
  simp only [CollatzResearch.WordTrace]
  refine ⟨14046895245110270755038035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149833549281176221387072373 14046895245110270755038035)
  ·
    refine ⟨21070342867665406132557053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14046895245110270755038035 21070342867665406132557053)
    ·
      refine ⟨7901378575374527299708895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21070342867665406132557053 7901378575374527299708895)
      ·
        refine ⟨11852067863061790949563343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7901378575374527299708895 11852067863061790949563343)
        ·
          refine ⟨17778101794592686424345015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11852067863061790949563343 17778101794592686424345015)
          ·
            refine ⟨26667152691889029636517523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17778101794592686424345015 26667152691889029636517523)
            ·
              refine ⟨40000729037833544454776285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26667152691889029636517523 40000729037833544454776285)
              ·
                refine ⟨15000273389187579170541107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40000729037833544454776285 15000273389187579170541107)
                ·
                  refine ⟨22500410083781368755811661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15000273389187579170541107 22500410083781368755811661)
                  ·
                    refine ⟨8437653781418013283429373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22500410083781368755811661 8437653781418013283429373)
                    ·
                      refine ⟨3164120168031754981286015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8437653781418013283429373 3164120168031754981286015)
                      ·
                        rfl

theorem cell23_6162102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_6162102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162102 prefixEnd_6162102 := by exact prefixLift 6162102
  have htrace : WordTrace (prefixWord ++ tailWord_6162102) baseStart_6162102 baseEnd_6162102 := by
    simpa [prefixWord, tailWord_6162102, baseEnd_6162102] using wordTrace_append hprefix tailTrace_6162102
  have hstable : (prefixWord ++ tailWord_6162102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162102).length < 2 ^ (prefixWord ++ tailWord_6162102).sum := by decide
  have hdescent : baseEnd_6162102 < baseStart_6162102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162129 : List Nat := [1, 2, 2, 1, 2, 6, 2, 1, 1, 3, 2]
def baseStart_6162129 : Nat := 118140960795 + 6162129 * 2 ^ 59
def prefixEnd_6162129 : Nat := 4983230072969 + 3 ^ 40 * 6162129 * 2
def baseEnd_6162129 : Nat := 3164134032009426375648391

theorem tailTrace_6162129 : CollatzResearch.WordTrace tailWord_6162129 prefixEnd_6162129 3164134032009426375648391 := by
  unfold tailWord_6162129
  simp only [CollatzResearch.WordTrace]
  refine ⟨224751308692666515691841441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149834205795111010461227627 224751308692666515691841441)
  ·
    refine ⟨168563481519499886768881081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224751308692666515691841441 168563481519499886768881081)
    ·
      refine ⟨126422611139624915076660811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168563481519499886768881081 126422611139624915076660811)
      ·
        refine ⟨189633916709437372614991217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126422611139624915076660811 189633916709437372614991217)
        ·
          refine ⟨142225437532078029461243413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189633916709437372614991217 142225437532078029461243413)
          ·
            refine ⟨6666817384316157630995785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142225437532078029461243413 6666817384316157630995785)
            ·
              refine ⟨5000113038237118223246839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6666817384316157630995785 5000113038237118223246839)
              ·
                refine ⟨7500169557355677334870259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5000113038237118223246839 7500169557355677334870259)
                ·
                  refine ⟨11250254336033516002305389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7500169557355677334870259 11250254336033516002305389)
                  ·
                    refine ⟨4218845376012568500864521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11250254336033516002305389 4218845376012568500864521)
                    ·
                      refine ⟨3164134032009426375648391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4218845376012568500864521 3164134032009426375648391)
                      ·
                        rfl

theorem cell23_6162129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 1, 3, 2].length) (baseStart_6162129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162129 prefixEnd_6162129 := by exact prefixLift 6162129
  have htrace : WordTrace (prefixWord ++ tailWord_6162129) baseStart_6162129 baseEnd_6162129 := by
    simpa [prefixWord, tailWord_6162129, baseEnd_6162129] using wordTrace_append hprefix tailTrace_6162129
  have hstable : (prefixWord ++ tailWord_6162129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162129).length < 2 ^ (prefixWord ++ tailWord_6162129).sum := by decide
  have hdescent : baseEnd_6162129 < baseStart_6162129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162138 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_6162138 : Nat := 118140960795 + 6162138 * 2 ^ 59
def prefixEnd_6162138 : Nat := 4983230072969 + 3 ^ 40 * 6162138 * 2
def baseEnd_6162138 : Nat := 3164138653335316840435849

theorem tailTrace_6162138 : CollatzResearch.WordTrace tailWord_6162138 prefixEnd_6162138 3164138653335316840435849 := by
  unfold tailWord_6162138
  simp only [CollatzResearch.WordTrace]
  refine ⟨56187909237408477557229767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149834424633089273485946045 56187909237408477557229767)
  ·
    refine ⟨84281863856112716335844651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56187909237408477557229767 84281863856112716335844651)
    ·
      refine ⟨126422795784169074503766977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84281863856112716335844651 126422795784169074503766977)
      ·
        refine ⟨94817096838126805877825233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126422795784169074503766977 94817096838126805877825233)
        ·
          refine ⟨71112822628595104408368925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94817096838126805877825233 71112822628595104408368925)
          ·
            refine ⟨26667308485723164153138347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71112822628595104408368925 26667308485723164153138347)
            ·
              refine ⟨40000962728584746229707521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26667308485723164153138347 40000962728584746229707521)
              ·
                refine ⟨30000722046438559672280641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40000962728584746229707521 30000722046438559672280641)
                ·
                  refine ⟨22500541534828919754210481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30000722046438559672280641 22500541534828919754210481)
                  ·
                    refine ⟨16875406151121689815657861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22500541534828919754210481 16875406151121689815657861)
                    ·
                      refine ⟨3164138653335316840435849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16875406151121689815657861 3164138653335316840435849)
                      ·
                        rfl

theorem cell23_6162138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_6162138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162138 prefixEnd_6162138 := by exact prefixLift 6162138
  have htrace : WordTrace (prefixWord ++ tailWord_6162138) baseStart_6162138 baseEnd_6162138 := by
    simpa [prefixWord, tailWord_6162138, baseEnd_6162138] using wordTrace_append hprefix tailTrace_6162138
  have hstable : (prefixWord ++ tailWord_6162138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162138).length < 2 ^ (prefixWord ++ tailWord_6162138).sum := by decide
  have hdescent : baseEnd_6162138 < baseStart_6162138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162148 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 7]
def baseStart_6162148 : Nat := 118140960795 + 6162148 * 2 ^ 59
def prefixEnd_6162148 : Nat := 4983230072969 + 3 ^ 40 * 6162148 * 2
def baseEnd_6162148 : Nat := 351571532015762422367867

theorem tailTrace_6162148 : CollatzResearch.WordTrace tailWord_6162148 prefixEnd_6162148 351571532015762422367867 := by
  unfold tailWord_6162148
  simp only [CollatzResearch.WordTrace]
  refine ⟨112376000839798840968391549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149834667786398454624522065 112376000839798840968391549)
  ·
    refine ⟨42141000314924565363146831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112376000839798840968391549 42141000314924565363146831)
    ·
      refine ⟨63211500472386848044720247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42141000314924565363146831 63211500472386848044720247)
      ·
        refine ⟨94817250708580272067080371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63211500472386848044720247 94817250708580272067080371)
        ·
          refine ⟨142225876062870408100620557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94817250708580272067080371 142225876062870408100620557)
          ·
            refine ⟨53334703523576403037732709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142225876062870408100620557 53334703523576403037732709)
            ·
              refine ⟨10000256910670575569574883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53334703523576403037732709 10000256910670575569574883)
              ·
                refine ⟨15000385366005863354362325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10000256910670575569574883 15000385366005863354362325)
                ·
                  refine ⟨351571532015762422367867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15000385366005863354362325 351571532015762422367867)
                  ·
                    rfl

theorem cell23_6162148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_6162148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162148 prefixEnd_6162148 := by exact prefixLift 6162148
  have htrace : WordTrace (prefixWord ++ tailWord_6162148) baseStart_6162148 baseEnd_6162148 := by
    simpa [prefixWord, tailWord_6162148, baseEnd_6162148] using wordTrace_append hprefix tailTrace_6162148
  have hstable : (prefixWord ++ tailWord_6162148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162148).length < 2 ^ (prefixWord ++ tailWord_6162148).sum := by decide
  have hdescent : baseEnd_6162148 < baseStart_6162148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162159 : List Nat := [1, 1, 2, 1, 5, 1, 5, 1, 2, 2, 2]
def baseStart_6162159 : Nat := 118140960795 + 6162159 * 2 ^ 59
def prefixEnd_6162159 : Nat := 4983230072969 + 3 ^ 40 * 6162159 * 2
def baseEnd_6162159 : Nat := 3164149436429061258273253

theorem tailTrace_6162159 : CollatzResearch.WordTrace tailWord_6162159 prefixEnd_6162159 3164149436429061258273253 := by
  unfold tailWord_6162159
  simp only [CollatzResearch.WordTrace]
  refine ⟨224752402882557830815433531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149834935255038553876955687 224752402882557830815433531)
  ·
    refine ⟨337128604323836746223150297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224752402882557830815433531 337128604323836746223150297)
    ·
      refine ⟨252846453242877559667362723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337128604323836746223150297 252846453242877559667362723)
      ·
        refine ⟨379269679864316339501044085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252846453242877559667362723 379269679864316339501044085)
        ·
          refine ⟨35556532487279656828222883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 379269679864316339501044085 35556532487279656828222883)
          ·
            refine ⟨53334798730919485242334325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35556532487279656828222883 53334798730919485242334325)
            ·
              refine ⟨5000137381023701741468843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53334798730919485242334325 5000137381023701741468843)
              ·
                refine ⟨7500206071535552612203265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5000137381023701741468843 7500206071535552612203265)
                ·
                  refine ⟨5625154553651664459152449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7500206071535552612203265 5625154553651664459152449)
                  ·
                    refine ⟨4218865915238748344364337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5625154553651664459152449 4218865915238748344364337)
                    ·
                      refine ⟨3164149436429061258273253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4218865915238748344364337 3164149436429061258273253)
                      ·
                        rfl

theorem cell23_6162159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 2, 2, 2].length) (baseStart_6162159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162159 prefixEnd_6162159 := by exact prefixLift 6162159
  have htrace : WordTrace (prefixWord ++ tailWord_6162159) baseStart_6162159 baseEnd_6162159 := by
    simpa [prefixWord, tailWord_6162159, baseEnd_6162159] using wordTrace_append hprefix tailTrace_6162159
  have hstable : (prefixWord ++ tailWord_6162159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162159).length < 2 ^ (prefixWord ++ tailWord_6162159).sum := by decide
  have hdescent : baseEnd_6162159 < baseStart_6162159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162171 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 7]
def baseStart_6162171 : Nat := 118140960795 + 6162171 * 2 ^ 59
def prefixEnd_6162171 : Nat := 4983230072969 + 3 ^ 40 * 6162171 * 2
def baseEnd_6162171 : Nat := 3164155598196915211323197

theorem tailTrace_6162171 : CollatzResearch.WordTrace tailWord_6162171 prefixEnd_6162171 3164155598196915211323197 := by
  unfold tailWord_6162171
  simp only [CollatzResearch.WordTrace]
  refine ⟨224752840558514356864870367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149835227039009571243246911 224752840558514356864870367)
  ·
    refine ⟨337129260837771535297305551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224752840558514356864870367 337129260837771535297305551)
    ·
      refine ⟨505693891256657302945958327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337129260837771535297305551 505693891256657302945958327)
      ·
        refine ⟨758540836884985954418937491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505693891256657302945958327 758540836884985954418937491)
        ·
          refine ⟨1137811255327478931628406237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758540836884985954418937491 1137811255327478931628406237)
          ·
            refine ⟨426679220747804599360652339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1137811255327478931628406237 426679220747804599360652339)
            ·
              refine ⟨640018831121706899040978509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426679220747804599360652339 640018831121706899040978509)
              ·
                refine ⟨240007061670640087140366941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 640018831121706899040978509 240007061670640087140366941)
                ·
                  refine ⟨90002648126490032677637603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240007061670640087140366941 90002648126490032677637603)
                  ·
                    refine ⟨135003972189735049016456405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90002648126490032677637603 135003972189735049016456405)
                    ·
                      refine ⟨3164155598196915211323197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135003972189735049016456405 3164155598196915211323197)
                      ·
                        rfl

theorem cell23_6162171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_6162171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162171 prefixEnd_6162171 := by exact prefixLift 6162171
  have htrace : WordTrace (prefixWord ++ tailWord_6162171) baseStart_6162171 baseEnd_6162171 := by
    simpa [prefixWord, tailWord_6162171, baseEnd_6162171] using wordTrace_append hprefix tailTrace_6162171
  have hstable : (prefixWord ++ tailWord_6162171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162171).length < 2 ^ (prefixWord ++ tailWord_6162171).sum := by decide
  have hdescent : baseEnd_6162171 < baseStart_6162171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162285 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_6162285 : Nat := 118140960795 + 6162285 * 2 ^ 59
def prefixEnd_6162285 : Nat := 4983230072969 + 3 ^ 40 * 6162285 * 2
def baseEnd_6162285 : Nat := 1054738044997175921765891

theorem tailTrace_6162285 : CollatzResearch.WordTrace tailWord_6162285 prefixEnd_6162285 1054738044997175921765891 := by
  unfold tailWord_6162285
  simp only [CollatzResearch.WordTrace]
  refine ⟨224756998480101354334520309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149837998986734236223013539 224756998480101354334520309)
  ·
    refine ⟨21070968607509501968861279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224756998480101354334520309 21070968607509501968861279)
    ·
      refine ⟨31606452911264252953291919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21070968607509501968861279 31606452911264252953291919)
      ·
        refine ⟨47409679366896379429937879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31606452911264252953291919 47409679366896379429937879)
        ·
          refine ⟨71114519050344569144906819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47409679366896379429937879 71114519050344569144906819)
          ·
            refine ⟨106671778575516853717360229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71114519050344569144906819 106671778575516853717360229)
            ·
              refine ⟨20000958482909410072005043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106671778575516853717360229 20000958482909410072005043)
              ·
                refine ⟨30001437724364115108007565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20000958482909410072005043 30001437724364115108007565)
                ·
                  refine ⟨11250539146636543165502837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30001437724364115108007565 11250539146636543165502837)
                  ·
                    refine ⟨1054738044997175921765891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11250539146636543165502837 1054738044997175921765891)
                    ·
                      rfl

theorem cell23_6162285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_6162285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162285 prefixEnd_6162285 := by exact prefixLift 6162285
  have htrace : WordTrace (prefixWord ++ tailWord_6162285) baseStart_6162285 baseEnd_6162285 := by
    simpa [prefixWord, tailWord_6162285, baseEnd_6162285] using wordTrace_append hprefix tailTrace_6162285
  have hstable : (prefixWord ++ tailWord_6162285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162285).length < 2 ^ (prefixWord ++ tailWord_6162285).sum := by decide
  have hdescent : baseEnd_6162285 < baseStart_6162285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162325 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_6162325 : Nat := 118140960795 + 6162325 * 2 ^ 59
def prefixEnd_6162325 : Nat := 4983230072969 + 3 ^ 40 * 6162325 * 2
def baseEnd_6162325 : Nat := 3164234674217707608797489

theorem tailTrace_6162325 : CollatzResearch.WordTrace tailWord_6162325 prefixEnd_6162325 3164234674217707608797489 := by
  unfold tailWord_6162325
  simp only [CollatzResearch.WordTrace]
  refine ⟨224758457399956441165976429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149838971599970960777317619 224758457399956441165976429)
  ·
    refine ⟨84284421524983665437241161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224758457399956441165976429 84284421524983665437241161)
    ·
      refine ⟨63213316143737749077930871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84284421524983665437241161 63213316143737749077930871)
      ·
        refine ⟨94819974215606623616896307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63213316143737749077930871 94819974215606623616896307)
        ·
          refine ⟨142229961323409935425344461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94819974215606623616896307 142229961323409935425344461)
          ·
            refine ⟨53336235496278725784504173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142229961323409935425344461 53336235496278725784504173)
            ·
              refine ⟨20001088311104522169189065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53336235496278725784504173 20001088311104522169189065)
              ·
                refine ⟨15000816233328391626891799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20001088311104522169189065 15000816233328391626891799)
                ·
                  refine ⟨22501224349992587440337699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15000816233328391626891799 22501224349992587440337699)
                  ·
                    refine ⟨33751836524988881160506549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22501224349992587440337699 33751836524988881160506549)
                    ·
                      refine ⟨3164234674217707608797489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33751836524988881160506549 3164234674217707608797489)
                      ·
                        rfl

theorem cell23_6162325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_6162325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162325 prefixEnd_6162325 := by exact prefixLift 6162325
  have htrace : WordTrace (prefixWord ++ tailWord_6162325) baseStart_6162325 baseEnd_6162325 := by
    simpa [prefixWord, tailWord_6162325, baseEnd_6162325] using wordTrace_append hprefix tailTrace_6162325
  have hstable : (prefixWord ++ tailWord_6162325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162325).length < 2 ^ (prefixWord ++ tailWord_6162325).sum := by decide
  have hdescent : baseEnd_6162325 < baseStart_6162325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162332 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 1, 6]
def baseStart_6162332 : Nat := 118140960795 + 6162332 * 2 ^ 59
def prefixEnd_6162332 : Nat := 4983230072969 + 3 ^ 40 * 6162332 * 2
def baseEnd_6162332 : Nat := 1054746089527429693803319

theorem tailTrace_6162332 : CollatzResearch.WordTrace tailWord_6162332 prefixEnd_6162332 1054746089527429693803319 := by
  unfold tailWord_6162332
  simp only [CollatzResearch.WordTrace]
  refine ⟨112379356355465540680740625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149839141807287387574320833 112379356355465540680740625)
  ·
    refine ⟨84284517266599155510555469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112379356355465540680740625 84284517266599155510555469)
    ·
      refine ⟨31606693974974683316458301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84284517266599155510555469 31606693974974683316458301)
      ·
        refine ⟨11852510240615506243671863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31606693974974683316458301 11852510240615506243671863)
        ·
          refine ⟨17778765360923259365507795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11852510240615506243671863 17778765360923259365507795)
          ·
            refine ⟨26668148041384889048261693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17778765360923259365507795 26668148041384889048261693)
            ·
              refine ⟨10000555515519333393098135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26668148041384889048261693 10000555515519333393098135)
              ·
                refine ⟨15000833273279000089647203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10000555515519333393098135 15000833273279000089647203)
                ·
                  refine ⟨22501249909918500134470805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15000833273279000089647203 22501249909918500134470805)
                  ·
                    refine ⟨1054746089527429693803319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22501249909918500134470805 1054746089527429693803319)
                    ·
                      rfl

theorem cell23_6162332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_6162332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162332 prefixEnd_6162332 := by exact prefixLift 6162332
  have htrace : WordTrace (prefixWord ++ tailWord_6162332) baseStart_6162332 baseEnd_6162332 := by
    simpa [prefixWord, tailWord_6162332, baseEnd_6162332] using wordTrace_append hprefix tailTrace_6162332
  have hstable : (prefixWord ++ tailWord_6162332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162332).length < 2 ^ (prefixWord ++ tailWord_6162332).sum := by decide
  have hdescent : baseEnd_6162332 < baseStart_6162332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162355 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 3]
def baseStart_6162355 : Nat := 118140960795 + 6162355 * 2 ^ 59
def prefixEnd_6162355 : Nat := 4983230072969 + 3 ^ 40 * 6162355 * 2
def baseEnd_6162355 : Nat := 3164250078637342491422351

theorem tailTrace_6162355 : CollatzResearch.WordTrace tailWord_6162355 prefixEnd_6162355 3164250078637342491422351 := by
  unfold tailWord_6162355
  simp only [CollatzResearch.WordTrace]
  refine ⟨224759551589847756289568519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149839701059898504193045679 224759551589847756289568519)
  ·
    refine ⟨337139327384771634434352779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224759551589847756289568519 337139327384771634434352779)
    ·
      refine ⟨505708991077157451651529169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337139327384771634434352779 505708991077157451651529169)
      ·
        refine ⟨379281743307868088738646877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505708991077157451651529169 379281743307868088738646877)
        ·
          refine ⟨142230653740450533276992579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379281743307868088738646877 142230653740450533276992579)
          ·
            refine ⟨213345980610675799915488869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142230653740450533276992579 213345980610675799915488869)
            ·
              refine ⟨40002371364501712484154163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213345980610675799915488869 40002371364501712484154163)
              ·
                refine ⟨60003557046752568726231245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40002371364501712484154163 60003557046752568726231245)
                ·
                  refine ⟨22501333892532213272336717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60003557046752568726231245 22501333892532213272336717)
                  ·
                    refine ⟨8438000209699579977126269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22501333892532213272336717 8438000209699579977126269)
                    ·
                      refine ⟨3164250078637342491422351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8438000209699579977126269 3164250078637342491422351)
                      ·
                        rfl

theorem cell23_6162355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 3].length) (baseStart_6162355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162355 prefixEnd_6162355 := by exact prefixLift 6162355
  have htrace : WordTrace (prefixWord ++ tailWord_6162355) baseStart_6162355 baseEnd_6162355 := by
    simpa [prefixWord, tailWord_6162355, baseEnd_6162355] using wordTrace_append hprefix tailTrace_6162355
  have hstable : (prefixWord ++ tailWord_6162355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162355).length < 2 ^ (prefixWord ++ tailWord_6162355).sum := by decide
  have hdescent : baseEnd_6162355 < baseStart_6162355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162399 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 3, 3, 2]
def baseStart_6162399 : Nat := 118140960795 + 6162399 * 2 ^ 59
def prefixEnd_6162399 : Nat := 4983230072969 + 3 ^ 40 * 6162399 * 2
def baseEnd_6162399 : Nat := 3164272671786140319272149

theorem tailTrace_6162399 : CollatzResearch.WordTrace tailWord_6162399 prefixEnd_6162399 3164272671786140319272149 := by
  unfold tailWord_6162399
  simp only [CollatzResearch.WordTrace]
  refine ⟨224761156401688351804170251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149840770934458901202780167 224761156401688351804170251)
  ·
    refine ⟨337141734602532527706255377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224761156401688351804170251 337141734602532527706255377)
    ·
      refine ⟨252856300951899395779691533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337141734602532527706255377 252856300951899395779691533)
      ·
        refine ⟨94821112856962273417384325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252856300951899395779691533 94821112856962273417384325)
        ·
          refine ⟨17778958660680426265759561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94821112856962273417384325 17778958660680426265759561)
          ·
            refine ⟨13334218995510319699319671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17778958660680426265759561 13334218995510319699319671)
            ·
              refine ⟨20001328493265479548979507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13334218995510319699319671 20001328493265479548979507)
              ·
                refine ⟨30001992739898219323469261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20001328493265479548979507 30001992739898219323469261)
                ·
                  refine ⟨11250747277461832246300973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30001992739898219323469261 11250747277461832246300973)
                  ·
                    refine ⟨4219030229048187092362865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11250747277461832246300973 4219030229048187092362865)
                    ·
                      refine ⟨3164272671786140319272149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219030229048187092362865 3164272671786140319272149)
                      ·
                        rfl

theorem cell23_6162399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_6162399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162399 prefixEnd_6162399 := by exact prefixLift 6162399
  have htrace : WordTrace (prefixWord ++ tailWord_6162399) baseStart_6162399 baseEnd_6162399 := by
    simpa [prefixWord, tailWord_6162399, baseEnd_6162399] using wordTrace_append hprefix tailTrace_6162399
  have hstable : (prefixWord ++ tailWord_6162399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162399).length < 2 ^ (prefixWord ++ tailWord_6162399).sum := by decide
  have hdescent : baseEnd_6162399 < baseStart_6162399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162415 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 5]
def baseStart_6162415 : Nat := 118140960795 + 6162415 * 2 ^ 59
def prefixEnd_6162415 : Nat := 4983230072969 + 3 ^ 40 * 6162415 * 2
def baseEnd_6162415 : Nat := 3164280887476612256672075

theorem tailTrace_6162415 : CollatzResearch.WordTrace tailWord_6162415 prefixEnd_6162415 3164280887476612256672075 := by
  unfold tailWord_6162415
  simp only [CollatzResearch.WordTrace]
  refine ⟨224761739969630386536752699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149841159979753591024501799 224761739969630386536752699)
  ·
    refine ⟨337142609954445579805129049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224761739969630386536752699 337142609954445579805129049)
    ·
      refine ⟨252856957465834184853846787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337142609954445579805129049 252856957465834184853846787)
      ·
        refine ⟨379285436198751277280770181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252856957465834184853846787 379285436198751277280770181)
        ·
          refine ⟨71116019287265864490144409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 379285436198751277280770181 71116019287265864490144409)
          ·
            refine ⟨53337014465449398367608307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71116019287265864490144409 53337014465449398367608307)
            ·
              refine ⟨80005521698174097551412461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53337014465449398367608307 80005521698174097551412461)
              ·
                refine ⟨30002070636815286581779673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80005521698174097551412461 30002070636815286581779673)
                ·
                  refine ⟨22501552977611464936334755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30002070636815286581779673 22501552977611464936334755)
                  ·
                    refine ⟨33752329466417197404502133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22501552977611464936334755 33752329466417197404502133)
                    ·
                      refine ⟨3164280887476612256672075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33752329466417197404502133 3164280887476612256672075)
                      ·
                        rfl

theorem cell23_6162415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_6162415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162415 prefixEnd_6162415 := by exact prefixLift 6162415
  have htrace : WordTrace (prefixWord ++ tailWord_6162415) baseStart_6162415 baseEnd_6162415 := by
    simpa [prefixWord, tailWord_6162415, baseEnd_6162415] using wordTrace_append hprefix tailTrace_6162415
  have hstable : (prefixWord ++ tailWord_6162415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162415).length < 2 ^ (prefixWord ++ tailWord_6162415).sum := by decide
  have hdescent : baseEnd_6162415 < baseStart_6162415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162429 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 4, 2, 2]
def baseStart_6162429 : Nat := 118140960795 + 6162429 * 2 ^ 59
def prefixEnd_6162429 : Nat := 4983230072969 + 3 ^ 40 * 6162429 * 2
def baseEnd_6162429 : Nat := 3164288076205775201897011

theorem tailTrace_6162429 : CollatzResearch.WordTrace tailWord_6162429 prefixEnd_6162429 3164288076205775201897011 := by
  unfold tailWord_6162429
  simp only [CollatzResearch.WordTrace]
  refine ⟨224762250591579666927762341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149841500394386444618508227 224762250591579666927762341)
  ·
    refine ⟨42142921985921187548955439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224762250591579666927762341 42142921985921187548955439)
    ·
      refine ⟨63214382978881781323433159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42142921985921187548955439 63214382978881781323433159)
      ·
        refine ⟨94821574468322671985149739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63214382978881781323433159 94821574468322671985149739)
        ·
          refine ⟨142232361702484007977724609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94821574468322671985149739 142232361702484007977724609)
          ·
            refine ⟨106674271276863005983293457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142232361702484007977724609 106674271276863005983293457)
            ·
              refine ⟨80005703457647254487470093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106674271276863005983293457 80005703457647254487470093)
              ·
                refine ⟨30002138796617720432801285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80005703457647254487470093 30002138796617720432801285)
                ·
                  refine ⟨5625401024365822581150241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30002138796617720432801285 5625401024365822581150241)
                  ·
                    refine ⟨4219050768274366935862681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5625401024365822581150241 4219050768274366935862681)
                    ·
                      refine ⟨3164288076205775201897011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219050768274366935862681 3164288076205775201897011)
                      ·
                        rfl

theorem cell23_6162429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_6162429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162429 prefixEnd_6162429 := by exact prefixLift 6162429
  have htrace : WordTrace (prefixWord ++ tailWord_6162429) baseStart_6162429 baseEnd_6162429 := by
    simpa [prefixWord, tailWord_6162429, baseEnd_6162429] using wordTrace_append hprefix tailTrace_6162429
  have hstable : (prefixWord ++ tailWord_6162429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162429).length < 2 ^ (prefixWord ++ tailWord_6162429).sum := by decide
  have hdescent : baseEnd_6162429 < baseStart_6162429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162446 : List Nat := [4, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2]
def baseStart_6162446 : Nat := 118140960795 + 6162446 * 2 ^ 59
def prefixEnd_6162446 : Nat := 4983230072969 + 3 ^ 40 * 6162446 * 2
def baseEnd_6162446 : Nat := 3164296805376901635384433

theorem tailTrace_6162446 : CollatzResearch.WordTrace tailWord_6162446 prefixEnd_6162446 3164296805376901635384433 := by
  unfold tailWord_6162446
  simp only [CollatzResearch.WordTrace]
  refine ⟨28095358829064759853891399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149841913755012052554087461 28095358829064759853891399)
  ·
    refine ⟨42143038243597139780837099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28095358829064759853891399 42143038243597139780837099)
    ·
      refine ⟨63214557365395709671255649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42143038243597139780837099 63214557365395709671255649)
      ·
        refine ⟨47410918024046782253441737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63214557365395709671255649 47410918024046782253441737)
        ·
          refine ⟨35558188518035086690081303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47410918024046782253441737 35558188518035086690081303)
          ·
            refine ⟨53337282777052630035121955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35558188518035086690081303 53337282777052630035121955)
            ·
              refine ⟨80005924165578945052682933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53337282777052630035121955 80005924165578945052682933)
              ·
                refine ⟨7500555390523026098689025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80005924165578945052682933 7500555390523026098689025)
                ·
                  refine ⟨5625416542892269574016769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7500555390523026098689025 5625416542892269574016769)
                  ·
                    refine ⟨4219062407169202180512577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5625416542892269574016769 4219062407169202180512577)
                    ·
                      refine ⟨3164296805376901635384433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219062407169202180512577 3164296805376901635384433)
                      ·
                        rfl

theorem cell23_6162446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_6162446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162446 prefixEnd_6162446 := by exact prefixLift 6162446
  have htrace : WordTrace (prefixWord ++ tailWord_6162446) baseStart_6162446 baseEnd_6162446 := by
    simpa [prefixWord, tailWord_6162446, baseEnd_6162446] using wordTrace_append hprefix tailTrace_6162446
  have hstable : (prefixWord ++ tailWord_6162446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162446).length < 2 ^ (prefixWord ++ tailWord_6162446).sum := by decide
  have hdescent : baseEnd_6162446 < baseStart_6162446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162469 : List Nat := [1, 3, 1, 2, 2, 4, 2, 3, 5]
def baseStart_6162469 : Nat := 118140960795 + 6162469 * 2 ^ 59
def prefixEnd_6162469 : Nat := 4983230072969 + 3 ^ 40 * 6162469 * 2
def baseEnd_6162469 : Nat := 351589846159106116155203

theorem tailTrace_6162469 : CollatzResearch.WordTrace tailWord_6162469 prefixEnd_6162469 351589846159106116155203 := by
  unfold tailWord_6162469
  simp only [CollatzResearch.WordTrace]
  refine ⟨224763709511434753759218461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149842473007623169172812307 224763709511434753759218461)
  ·
    refine ⟨84286391066788032659706923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224763709511434753759218461 84286391066788032659706923)
    ·
      refine ⟨126429586600182048989560385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84286391066788032659706923 126429586600182048989560385)
      ·
        refine ⟨94822189950136536742170289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126429586600182048989560385 94822189950136536742170289)
        ·
          refine ⟨71116642462602402556627717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94822189950136536742170289 71116642462602402556627717)
          ·
            refine ⟨13334370461737950479367697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71116642462602402556627717 13334370461737950479367697)
            ·
              refine ⟨10000777846303462859525773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13334370461737950479367697 10000777846303462859525773)
              ·
                refine ⟨3750291692363798572322165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10000777846303462859525773 3750291692363798572322165)
                ·
                  refine ⟨351589846159106116155203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3750291692363798572322165 351589846159106116155203)
                  ·
                    rfl

theorem cell23_6162469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 5].length) (baseStart_6162469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162469 prefixEnd_6162469 := by exact prefixLift 6162469
  have htrace : WordTrace (prefixWord ++ tailWord_6162469) baseStart_6162469 baseEnd_6162469 := by
    simpa [prefixWord, tailWord_6162469, baseEnd_6162469] using wordTrace_append hprefix tailTrace_6162469
  have hstable : (prefixWord ++ tailWord_6162469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162469).length < 2 ^ (prefixWord ++ tailWord_6162469).sum := by decide
  have hdescent : baseEnd_6162469 < baseStart_6162469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162475 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 5]
def baseStart_6162475 : Nat := 118140960795 + 6162475 * 2 ^ 59
def prefixEnd_6162475 : Nat := 4983230072969 + 3 ^ 40 * 6162475 * 2
def baseEnd_6162475 : Nat := 3164311696315882021921799

theorem tailTrace_6162475 : CollatzResearch.WordTrace tailWord_6162475 prefixEnd_6162475 3164311696315882021921799 := by
  unfold tailWord_6162475
  simp only [CollatzResearch.WordTrace]
  refine ⟨224763928349413016783936879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149842618899608677855957919 224763928349413016783936879)
  ·
    refine ⟨337145892524119525175905319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224763928349413016783936879 337145892524119525175905319)
    ·
      refine ⟨505718838786179287763857979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337145892524119525175905319 505718838786179287763857979)
      ·
        refine ⟨758578258179268931645786969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505718838786179287763857979 758578258179268931645786969)
        ·
          refine ⟨568933693634451698734340227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 758578258179268931645786969 568933693634451698734340227)
          ·
            refine ⟨853400540451677548101510341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568933693634451698734340227 853400540451677548101510341)
            ·
              refine ⟨160012601334689540269033189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 853400540451677548101510341 160012601334689540269033189)
              ·
                refine ⟨30002362750254288800443723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160012601334689540269033189 30002362750254288800443723)
                ·
                  refine ⟨45003544125381433200665585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30002362750254288800443723 45003544125381433200665585)
                  ·
                    refine ⟨33752658094036074900499189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45003544125381433200665585 33752658094036074900499189)
                    ·
                      refine ⟨3164311696315882021921799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33752658094036074900499189 3164311696315882021921799)
                      ·
                        rfl

theorem cell23_6162475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 5].length) (baseStart_6162475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162475 prefixEnd_6162475 := by exact prefixLift 6162475
  have htrace : WordTrace (prefixWord ++ tailWord_6162475) baseStart_6162475 baseEnd_6162475 := by
    simpa [prefixWord, tailWord_6162475, baseEnd_6162475] using wordTrace_append hprefix tailTrace_6162475
  have hstable : (prefixWord ++ tailWord_6162475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162475).length < 2 ^ (prefixWord ++ tailWord_6162475).sum := by decide
  have hdescent : baseEnd_6162475 < baseStart_6162475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162522 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3]
def baseStart_6162522 : Nat := 118140960795 + 6162522 * 2 ^ 59
def prefixEnd_6162522 : Nat := 4983230072969 + 3 ^ 40 * 6162522 * 2
def baseEnd_6162522 : Nat := 3164335829906643338034083

theorem tailTrace_6162522 : CollatzResearch.WordTrace tailWord_6162522 prefixEnd_6162522 3164335829906643338034083 := by
  unfold tailWord_6162522
  simp only [CollatzResearch.WordTrace]
  refine ⟨56191410645060685952724455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149843761720161829207265213 56191410645060685952724455)
  ·
    refine ⟨84287115967591028929086683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56191410645060685952724455 84287115967591028929086683)
    ·
      refine ⟨126430673951386543393630025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84287115967591028929086683 126430673951386543393630025)
      ·
        refine ⟨94823005463539907545222519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126430673951386543393630025 94823005463539907545222519)
        ·
          refine ⟨142234508195309861317833779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94823005463539907545222519 142234508195309861317833779)
          ·
            refine ⟨213351762292964791976750669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142234508195309861317833779 213351762292964791976750669)
            ·
              refine ⟨80006910859861796991281501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213351762292964791976750669 80006910859861796991281501)
              ·
                refine ⟨30002591572448173871730563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80006910859861796991281501 30002591572448173871730563)
                ·
                  refine ⟨45003887358672260807595845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30002591572448173871730563 45003887358672260807595845)
                  ·
                    refine ⟨8438228879751048901424221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45003887358672260807595845 8438228879751048901424221)
                    ·
                      refine ⟨3164335829906643338034083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8438228879751048901424221 3164335829906643338034083)
                      ·
                        rfl

theorem cell23_6162522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_6162522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162522 prefixEnd_6162522 := by exact prefixLift 6162522
  have htrace : WordTrace (prefixWord ++ tailWord_6162522) baseStart_6162522 baseEnd_6162522 := by
    simpa [prefixWord, tailWord_6162522, baseEnd_6162522] using wordTrace_append hprefix tailTrace_6162522
  have hstable : (prefixWord ++ tailWord_6162522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162522).length < 2 ^ (prefixWord ++ tailWord_6162522).sum := by decide
  have hdescent : baseEnd_6162522 < baseStart_6162522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162542 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 8]
def baseStart_6162542 : Nat := 118140960795 + 6162542 * 2 ^ 59
def prefixEnd_6162542 : Nat := 4983230072969 + 3 ^ 40 * 6162542 * 2
def baseEnd_6162542 : Nat := 351594011057748139975999

theorem tailTrace_6162542 : CollatzResearch.WordTrace tailWord_6162542 prefixEnd_6162542 351594011057748139975999 := by
  unfold tailWord_6162542
  simp only [CollatzResearch.WordTrace]
  refine ⟨28095796505021285903328235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149844248026780191484417253 28095796505021285903328235)
  ·
    refine ⟨42143694757531928854992353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28095796505021285903328235 42143694757531928854992353)
    ·
      refine ⟨31607771068148946641244265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42143694757531928854992353 31607771068148946641244265)
      ·
        refine ⟨23705828301111709980933199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31607771068148946641244265 23705828301111709980933199)
        ·
          refine ⟨35558742451667564971399799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23705828301111709980933199 35558742451667564971399799)
          ·
            refine ⟨53338113677501347457099699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35558742451667564971399799 53338113677501347457099699)
            ·
              refine ⟨80007170516252021185649549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53338113677501347457099699 80007170516252021185649549)
              ·
                refine ⟨30002688943594507944618581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80007170516252021185649549 30002688943594507944618581)
                ·
                  refine ⟨351594011057748139975999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30002688943594507944618581 351594011057748139975999)
                  ·
                    rfl

theorem cell23_6162542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_6162542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162542 prefixEnd_6162542 := by exact prefixLift 6162542
  have htrace : WordTrace (prefixWord ++ tailWord_6162542) baseStart_6162542 baseEnd_6162542 := by
    simpa [prefixWord, tailWord_6162542, baseEnd_6162542] using wordTrace_append hprefix tailTrace_6162542
  have hstable : (prefixWord ++ tailWord_6162542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162542).length < 2 ^ (prefixWord ++ tailWord_6162542).sum := by decide
  have hdescent : baseEnd_6162542 < baseStart_6162542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162546 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_6162546 : Nat := 118140960795 + 6162546 * 2 ^ 59
def prefixEnd_6162546 : Nat := 4983230072969 + 3 ^ 40 * 6162546 * 2
def baseEnd_6162546 : Nat := 1054782717814117081377991

theorem tailTrace_6162546 : CollatzResearch.WordTrace tailWord_6162546 prefixEnd_6162546 1054782717814117081377991 := by
  unfold tailWord_6162546
  simp only [CollatzResearch.WordTrace]
  refine ⟨56191629483038948977442873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149844345288103863939847661 56191629483038948977442873)
  ·
    refine ⟨42143722112279211733082155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56191629483038948977442873 42143722112279211733082155)
    ·
      refine ⟨63215583168418817599623233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42143722112279211733082155 63215583168418817599623233)
      ·
        refine ⟨47411687376314113199717425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63215583168418817599623233 47411687376314113199717425)
        ·
          refine ⟨35558765532235584899788069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47411687376314113199717425 35558765532235584899788069)
          ·
            refine ⟨6667268537294172168710263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35558765532235584899788069 6667268537294172168710263)
            ·
              refine ⟨10000902805941258253065395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6667268537294172168710263 10000902805941258253065395)
              ·
                refine ⟨15001354208911887379598093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10000902805941258253065395 15001354208911887379598093)
                ·
                  refine ⟨5625507828341957767349285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15001354208911887379598093 5625507828341957767349285)
                  ·
                    refine ⟨1054782717814117081377991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5625507828341957767349285 1054782717814117081377991)
                    ·
                      rfl

theorem cell23_6162546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_6162546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162546 prefixEnd_6162546 := by exact prefixLift 6162546
  have htrace : WordTrace (prefixWord ++ tailWord_6162546) baseStart_6162546 baseEnd_6162546 := by
    simpa [prefixWord, tailWord_6162546, baseEnd_6162546] using wordTrace_append hprefix tailTrace_6162546
  have hstable : (prefixWord ++ tailWord_6162546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162546).length < 2 ^ (prefixWord ++ tailWord_6162546).sum := by decide
  have hdescent : baseEnd_6162546 < baseStart_6162546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162555 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 1, 11]
def baseStart_6162555 : Nat := 118140960795 + 6162555 * 2 ^ 59
def prefixEnd_6162555 : Nat := 4983230072969 + 3 ^ 40 * 6162555 * 2
def baseEnd_6162555 : Nat := 1054784258256080569640477

theorem tailTrace_6162555 : CollatzResearch.WordTrace tailWord_6162555 prefixEnd_6162555 1054784258256080569640477 := by
  unfold tailWord_6162555
  simp only [CollatzResearch.WordTrace]
  refine ⟨224766846189123190446849119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149844564126082126964566079 224766846189123190446849119)
  ·
    refine ⟨337150269283684785670273679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224766846189123190446849119 337150269283684785670273679)
    ·
      refine ⟨505725403925527178505410519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337150269283684785670273679 505725403925527178505410519)
      ·
        refine ⟨758588105888290767758115779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505725403925527178505410519 758588105888290767758115779)
        ·
          refine ⟨1137882158832436151637173669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758588105888290767758115779 1137882158832436151637173669)
          ·
            refine ⟨213352904781081778431970063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1137882158832436151637173669 213352904781081778431970063)
            ·
              refine ⟨320029357171622667647955095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213352904781081778431970063 320029357171622667647955095)
              ·
                refine ⟨480044035757434001471932643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320029357171622667647955095 480044035757434001471932643)
                ·
                  refine ⟨720066053636151002207898965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480044035757434001471932643 720066053636151002207898965)
                  ·
                    refine ⟨1054784258256080569640477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 720066053636151002207898965 1054784258256080569640477)
                    ·
                      rfl

theorem cell23_6162555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 11].length) (baseStart_6162555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162555 prefixEnd_6162555 := by exact prefixLift 6162555
  have htrace : WordTrace (prefixWord ++ tailWord_6162555) baseStart_6162555 baseEnd_6162555 := by
    simpa [prefixWord, tailWord_6162555, baseEnd_6162555] using wordTrace_append hprefix tailTrace_6162555
  have hstable : (prefixWord ++ tailWord_6162555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162555).length < 2 ^ (prefixWord ++ tailWord_6162555).sum := by decide
  have hdescent : baseEnd_6162555 < baseStart_6162555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162569 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 5, 1, 3]
def baseStart_6162569 : Nat := 118140960795 + 6162569 * 2 ^ 59
def prefixEnd_6162569 : Nat := 4983230072969 + 3 ^ 40 * 6162569 * 2
def baseEnd_6162569 : Nat := 3164359963497404654146367

theorem tailTrace_6162569 : CollatzResearch.WordTrace tailWord_6162569 prefixEnd_6162569 3164359963497404654146367 := by
  unfold tailWord_6162569
  simp only [CollatzResearch.WordTrace]
  refine ⟨224767356811072470837858761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149844904540714980558572507 224767356811072470837858761)
  ·
    refine ⟨168575517608304353128394071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224767356811072470837858761 168575517608304353128394071)
    ·
      refine ⟨252863276412456529692591107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168575517608304353128394071 252863276412456529692591107)
      ·
        refine ⟨379294914618684794538886661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252863276412456529692591107 379294914618684794538886661)
        ·
          refine ⟨71117796491003398976041249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 379294914618684794538886661 71117796491003398976041249)
          ·
            refine ⟨53338347368252549232030937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71117796491003398976041249 53338347368252549232030937)
            ·
              refine ⟨40003760526189411924023203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53338347368252549232030937 40003760526189411924023203)
              ·
                refine ⟨60005640789284117886034805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40003760526189411924023203 60005640789284117886034805)
                ·
                  refine ⟨5625528823995386051815763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60005640789284117886034805 5625528823995386051815763)
                  ·
                    refine ⟨8438293235993079077723645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5625528823995386051815763 8438293235993079077723645)
                    ·
                      refine ⟨3164359963497404654146367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8438293235993079077723645 3164359963497404654146367)
                      ·
                        rfl

theorem cell23_6162569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 1, 3].length) (baseStart_6162569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162569 prefixEnd_6162569 := by exact prefixLift 6162569
  have htrace : WordTrace (prefixWord ++ tailWord_6162569) baseStart_6162569 baseEnd_6162569 := by
    simpa [prefixWord, tailWord_6162569, baseEnd_6162569] using wordTrace_append hprefix tailTrace_6162569
  have hstable : (prefixWord ++ tailWord_6162569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162569).length < 2 ^ (prefixWord ++ tailWord_6162569).sum := by decide
  have hdescent : baseEnd_6162569 < baseStart_6162569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162619 : List Nat := [1, 1, 1, 1, 1, 2, 5, 5, 2, 4]
def baseStart_6162619 : Nat := 118140960795 + 6162619 * 2 ^ 59
def prefixEnd_6162619 : Nat := 4983230072969 + 3 ^ 40 * 6162619 * 2
def baseEnd_6162619 : Nat := 1054795212510043152840379

theorem tailTrace_6162619 : CollatzResearch.WordTrace tailWord_6162619 prefixEnd_6162619 1054795212510043152840379 := by
  unfold tailWord_6162619
  simp only [CollatzResearch.WordTrace]
  refine ⟨224769180460891329377178911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149846120307260886251452607 224769180460891329377178911)
  ·
    refine ⟨337153770691336994065768367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224769180460891329377178911 337153770691336994065768367)
    ·
      refine ⟨505730656037005491098652551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337153770691336994065768367 505730656037005491098652551)
      ·
        refine ⟨758595984055508236647978827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505730656037005491098652551 758595984055508236647978827)
        ·
          refine ⟨1137893976083262354971968241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758595984055508236647978827 1137893976083262354971968241)
          ·
            refine ⟨853420482062446766228976181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1137893976083262354971968241 853420482062446766228976181)
            ·
              refine ⟨80008170193354384333966517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 853420482062446766228976181 80008170193354384333966517)
              ·
                refine ⟨7500765955626973531309361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80008170193354384333966517 7500765955626973531309361)
                ·
                  refine ⟨5625574466720230148482021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7500765955626973531309361 5625574466720230148482021)
                  ·
                    refine ⟨1054795212510043152840379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5625574466720230148482021 1054795212510043152840379)
                    ·
                      rfl

theorem cell23_6162619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 4].length) (baseStart_6162619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162619 prefixEnd_6162619 := by exact prefixLift 6162619
  have htrace : WordTrace (prefixWord ++ tailWord_6162619) baseStart_6162619 baseEnd_6162619 := by
    simpa [prefixWord, tailWord_6162619, baseEnd_6162619] using wordTrace_append hprefix tailTrace_6162619
  have hstable : (prefixWord ++ tailWord_6162619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162619).length < 2 ^ (prefixWord ++ tailWord_6162619).sum := by decide
  have hdescent : baseEnd_6162619 < baseStart_6162619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162629 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 3, 2, 3]
def baseStart_6162629 : Nat := 118140960795 + 6162629 * 2 ^ 59
def prefixEnd_6162629 : Nat := 4983230072969 + 3 ^ 40 * 6162629 * 2
def baseEnd_6162629 : Nat := 3164390772336674419396091

theorem tailTrace_6162629 : CollatzResearch.WordTrace tailWord_6162629 prefixEnd_6162629 3164390772336674419396091 := by
  unfold tailWord_6162629
  simp only [CollatzResearch.WordTrace]
  refine ⟨224769545190855101085042941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149846363460570067390028627 224769545190855101085042941)
  ·
    refine ⟨84288579446570662906891103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224769545190855101085042941 84288579446570662906891103)
    ·
      refine ⟨126432869169855994360336655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84288579446570662906891103 126432869169855994360336655)
      ·
        refine ⟨189649303754783991540504983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126432869169855994360336655 189649303754783991540504983)
        ·
          refine ⟨284473955632175987310757475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189649303754783991540504983 284473955632175987310757475)
          ·
            refine ⟨426710933448263980966136213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284473955632175987310757475 426710933448263980966136213)
            ·
              refine ⟨20002075005387374107787635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 426710933448263980966136213 20002075005387374107787635)
              ·
                refine ⟨30003112508081061161681453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20002075005387374107787635 30003112508081061161681453)
                ·
                  refine ⟨11251167190530397935630545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30003112508081061161681453 11251167190530397935630545)
                  ·
                    refine ⟨8438375392897798451722909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11251167190530397935630545 8438375392897798451722909)
                    ·
                      refine ⟨3164390772336674419396091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8438375392897798451722909 3164390772336674419396091)
                      ·
                        rfl

theorem cell23_6162629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_6162629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162629 prefixEnd_6162629 := by exact prefixLift 6162629
  have htrace : WordTrace (prefixWord ++ tailWord_6162629) baseStart_6162629 baseEnd_6162629 := by
    simpa [prefixWord, tailWord_6162629, baseEnd_6162629] using wordTrace_append hprefix tailTrace_6162629
  have hstable : (prefixWord ++ tailWord_6162629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162629).length < 2 ^ (prefixWord ++ tailWord_6162629).sum := by decide
  have hdescent : baseEnd_6162629 < baseStart_6162629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162653 : List Nat := [1, 4, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_6162653 : Nat := 118140960795 + 6162653 * 2 ^ 59
def prefixEnd_6162653 : Nat := 4983230072969 + 3 ^ 40 * 6162653 * 2
def baseEnd_6162653 : Nat := 1054801031957460775165327

theorem tailTrace_6162653 : CollatzResearch.WordTrace tailWord_6162653 prefixEnd_6162653 1054801031957460775165327 := by
  unfold tailWord_6162653
  simp only [CollatzResearch.WordTrace]
  refine ⟨224770420542768153183916613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149846947028512102122611075 224770420542768153183916613)
  ·
    refine ⟨42144453851769028721984365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224770420542768153183916613 42144453851769028721984365)
    ·
      refine ⟨15804170194413385770744137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42144453851769028721984365 15804170194413385770744137)
      ·
        refine ⟨11853127645810039328058103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15804170194413385770744137 11853127645810039328058103)
        ·
          refine ⟨17779691468715058992087155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11853127645810039328058103 17779691468715058992087155)
          ·
            refine ⟨26669537203072588488130733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17779691468715058992087155 26669537203072588488130733)
            ·
              refine ⟨10001076451152220683049025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26669537203072588488130733 10001076451152220683049025)
              ·
                refine ⟨7500807338364165512286769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10001076451152220683049025 7500807338364165512286769)
                ·
                  refine ⟨5625605503773124134215077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7500807338364165512286769 5625605503773124134215077)
                  ·
                    refine ⟨1054801031957460775165327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5625605503773124134215077 1054801031957460775165327)
                    ·
                      rfl

theorem cell23_6162653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_6162653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162653 prefixEnd_6162653 := by exact prefixLift 6162653
  have htrace : WordTrace (prefixWord ++ tailWord_6162653) baseStart_6162653 baseEnd_6162653 := by
    simpa [prefixWord, tailWord_6162653, baseEnd_6162653] using wordTrace_append hprefix tailTrace_6162653
  have hstable : (prefixWord ++ tailWord_6162653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162653).length < 2 ^ (prefixWord ++ tailWord_6162653).sum := by decide
  have hdescent : baseEnd_6162653 < baseStart_6162653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162672 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 5]
def baseStart_6162672 : Nat := 118140960795 + 6162672 * 2 ^ 59
def prefixEnd_6162672 : Nat := 4983230072969 + 3 ^ 40 * 6162672 * 2
def baseEnd_6162672 : Nat := 3164412852004817751158393

theorem tailTrace_6162672 : CollatzResearch.WordTrace tailWord_6162672 prefixEnd_6162672 3164412852004817751158393 := by
  unfold tailWord_6162672
  simp only [CollatzResearch.WordTrace]
  refine ⟨112385556764849659714429135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149847409019799546285905513 112385556764849659714429135)
  ·
    refine ⟨168578335147274489571643703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112385556764849659714429135 168578335147274489571643703)
    ·
      refine ⟨252867502720911734357465555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168578335147274489571643703 252867502720911734357465555)
      ·
        refine ⟨379301254081367601536198333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252867502720911734357465555 379301254081367601536198333)
        ·
          refine ⟨142237970280512850576074375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379301254081367601536198333 142237970280512850576074375)
          ·
            refine ⟨213356955420769275864111563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142237970280512850576074375 213356955420769275864111563)
            ·
              refine ⟨320035433131153913796167345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213356955420769275864111563 320035433131153913796167345)
              ·
                refine ⟨240026574848365435347125509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320035433131153913796167345 240026574848365435347125509)
                ·
                  refine ⟨45004982784068519127586033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240026574848365435347125509 45004982784068519127586033)
                  ·
                    refine ⟨33753737088051389345689525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45004982784068519127586033 33753737088051389345689525)
                    ·
                      refine ⟨3164412852004817751158393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33753737088051389345689525 3164412852004817751158393)
                      ·
                        rfl

theorem cell23_6162672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_6162672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162672 prefixEnd_6162672 := by exact prefixLift 6162672
  have htrace : WordTrace (prefixWord ++ tailWord_6162672) baseStart_6162672 baseEnd_6162672 := by
    simpa [prefixWord, tailWord_6162672, baseEnd_6162672] using wordTrace_append hprefix tailTrace_6162672
  have hstable : (prefixWord ++ tailWord_6162672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162672).length < 2 ^ (prefixWord ++ tailWord_6162672).sum := by decide
  have hdescent : baseEnd_6162672 < baseStart_6162672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162737 : List Nat := [1, 2, 2, 3, 5, 1, 1, 2, 1, 3, 2]
def baseStart_6162737 : Nat := 118140960795 + 6162737 * 2 ^ 59
def prefixEnd_6162737 : Nat := 4983230072969 + 3 ^ 40 * 6162737 * 2
def baseEnd_6162737 : Nat := 3164446228247359996845595

theorem tailTrace_6162737 : CollatzResearch.WordTrace tailWord_6162737 prefixEnd_6162737 3164446228247359996845595 := by
  unfold tailWord_6162737
  simp only [CollatzResearch.WordTrace]
  refine ⟨224773484274463835529974465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149848989516309223686649643 224773484274463835529974465)
  ·
    refine ⟨168580113205847876647480849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224773484274463835529974465 168580113205847876647480849)
    ·
      refine ⟨126435084904385907485610637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168580113205847876647480849 126435084904385907485610637)
      ·
        refine ⟨47413156839144715307103989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126435084904385907485610637 47413156839144715307103989)
        ·
          refine ⟨4444983453669817060040999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47413156839144715307103989 4444983453669817060040999)
          ·
            refine ⟨6667475180504725590061499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4444983453669817060040999 6667475180504725590061499)
            ·
              refine ⟨10001212770757088385092249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6667475180504725590061499 10001212770757088385092249)
              ·
                refine ⟨7500909578067816288819187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10001212770757088385092249 7500909578067816288819187)
                ·
                  refine ⟨11251364367101724433228781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7500909578067816288819187 11251364367101724433228781)
                  ·
                    refine ⟨4219261637663146662460793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11251364367101724433228781 4219261637663146662460793)
                    ·
                      refine ⟨3164446228247359996845595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219261637663146662460793 3164446228247359996845595)
                      ·
                        rfl

theorem cell23_6162737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_6162737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162737 prefixEnd_6162737 := by exact prefixLift 6162737
  have htrace : WordTrace (prefixWord ++ tailWord_6162737) baseStart_6162737 baseEnd_6162737 := by
    simpa [prefixWord, tailWord_6162737, baseEnd_6162737] using wordTrace_append hprefix tailTrace_6162737
  have hstable : (prefixWord ++ tailWord_6162737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162737).length < 2 ^ (prefixWord ++ tailWord_6162737).sum := by decide
  have hdescent : baseEnd_6162737 < baseStart_6162737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162773 : List Nat := [1, 3, 2, 2, 4, 1, 1, 4, 5]
def baseStart_6162773 : Nat := 118140960795 + 6162773 * 2 ^ 59
def prefixEnd_6162773 : Nat := 4983230072969 + 3 ^ 40 * 6162773 * 2
def baseEnd_6162773 : Nat := 351607190394546872888381

theorem tailTrace_6162773 : CollatzResearch.WordTrace tailWord_6162773 prefixEnd_6162773 351607190394546872888381 := by
  unfold tailWord_6162773
  simp only [CollatzResearch.WordTrace]
  refine ⟨224774797302333413678284973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149849864868222275785523315 224774797302333413678284973)
  ·
    refine ⟨84290548988375030129356865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224774797302333413678284973 84290548988375030129356865)
    ·
      refine ⟨63217911741281272597017649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84290548988375030129356865 63217911741281272597017649)
      ·
        refine ⟨47413433805960954447763237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63217911741281272597017649 47413433805960954447763237)
        ·
          refine ⟨8890018838617678958955607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47413433805960954447763237 8890018838617678958955607)
          ·
            refine ⟨13335028257926518438433411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8890018838617678958955607 13335028257926518438433411)
            ·
              refine ⟨20002542386889777657650117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13335028257926518438433411 20002542386889777657650117)
              ·
                refine ⟨3750476697541833310809397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20002542386889777657650117 3750476697541833310809397)
                ·
                  refine ⟨351607190394546872888381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3750476697541833310809397 351607190394546872888381)
                  ·
                    rfl

theorem cell23_6162773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 5].length) (baseStart_6162773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162773 prefixEnd_6162773 := by exact prefixLift 6162773
  have htrace : WordTrace (prefixWord ++ tailWord_6162773) baseStart_6162773 baseEnd_6162773 := by
    simpa [prefixWord, tailWord_6162773, baseEnd_6162773] using wordTrace_append hprefix tailTrace_6162773
  have hstable : (prefixWord ++ tailWord_6162773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162773).length < 2 ^ (prefixWord ++ tailWord_6162773).sum := by decide
  have hdescent : baseEnd_6162773 < baseStart_6162773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
