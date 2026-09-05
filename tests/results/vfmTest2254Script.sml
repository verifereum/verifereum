Theory vfmTest2254[no_sig_docs]
Ancestors vfmTestDefs2254
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2254_0.nsv", "result2254_1.nsv", "result2254_2.nsv", "result2254_3.nsv", "result2254_4.nsv"];
val thyn = "vfmTestDefs2254";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
