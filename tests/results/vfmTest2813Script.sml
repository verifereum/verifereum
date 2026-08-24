Theory vfmTest2813[no_sig_docs]
Ancestors vfmTestDefs2813
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2813_0.nsv", "result2813_1.nsv", "result2813_2.nsv", "result2813_3.nsv"];
val thyn = "vfmTestDefs2813";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
