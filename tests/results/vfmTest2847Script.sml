Theory vfmTest2847[no_sig_docs]
Ancestors vfmTestDefs2847
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2847_0.nsv", "result2847_1.nsv", "result2847_2.nsv", "result2847_3.nsv"];
val thyn = "vfmTestDefs2847";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
