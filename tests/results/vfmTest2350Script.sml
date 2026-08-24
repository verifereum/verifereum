Theory vfmTest2350[no_sig_docs]
Ancestors vfmTestDefs2350
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2350_0.nsv", "result2350_1.nsv"];
val thyn = "vfmTestDefs2350";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
