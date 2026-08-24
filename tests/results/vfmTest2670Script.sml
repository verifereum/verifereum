Theory vfmTest2670[no_sig_docs]
Ancestors vfmTestDefs2670
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2670_0.nsv", "result2670_1.nsv", "result2670_2.nsv", "result2670_3.nsv"];
val thyn = "vfmTestDefs2670";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
