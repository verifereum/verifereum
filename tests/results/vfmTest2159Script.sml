Theory vfmTest2159[no_sig_docs]
Ancestors vfmTestDefs2159
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2159_0.nsv", "result2159_1.nsv", "result2159_2.nsv", "result2159_3.nsv", "result2159_4.nsv", "result2159_5.nsv"];
val thyn = "vfmTestDefs2159";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
