Theory vfmTest2668[no_sig_docs]
Ancestors vfmTestDefs2668
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2668_0.nsv", "result2668_1.nsv", "result2668_2.nsv", "result2668_3.nsv"];
val thyn = "vfmTestDefs2668";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
