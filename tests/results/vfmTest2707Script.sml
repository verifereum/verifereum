Theory vfmTest2707[no_sig_docs]
Ancestors vfmTestDefs2707
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2707_0.nsv", "result2707_1.nsv", "result2707_2.nsv", "result2707_3.nsv"];
val thyn = "vfmTestDefs2707";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
