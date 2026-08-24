Theory vfmTest2762[no_sig_docs]
Ancestors vfmTestDefs2762
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2762_0.nsv", "result2762_1.nsv", "result2762_2.nsv", "result2762_3.nsv"];
val thyn = "vfmTestDefs2762";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
