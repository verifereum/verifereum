Theory vfmTest2630[no_sig_docs]
Ancestors vfmTestDefs2630
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2630_0.nsv", "result2630_1.nsv", "result2630_2.nsv", "result2630_3.nsv"];
val thyn = "vfmTestDefs2630";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
