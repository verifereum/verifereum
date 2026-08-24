Theory vfmTest1943[no_sig_docs]
Ancestors vfmTestDefs1943
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1943_0.nsv", "result1943_1.nsv", "result1943_2.nsv", "result1943_3.nsv", "result1943_4.nsv", "result1943_5.nsv", "result1943_6.nsv", "result1943_7.nsv"];
val thyn = "vfmTestDefs1943";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
