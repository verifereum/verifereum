Theory vfmTest2689[no_sig_docs]
Ancestors vfmTestDefs2689
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2689_0.nsv", "result2689_1.nsv", "result2689_2.nsv"];
val thyn = "vfmTestDefs2689";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
