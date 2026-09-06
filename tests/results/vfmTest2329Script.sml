Theory vfmTest2329[no_sig_docs]
Ancestors vfmTestDefs2329
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2329_0.nsv", "result2329_1.nsv", "result2329_2.nsv", "result2329_3.nsv"];
val thyn = "vfmTestDefs2329";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
