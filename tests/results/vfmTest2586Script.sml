Theory vfmTest2586[no_sig_docs]
Ancestors vfmTestDefs2586
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2586_0.nsv", "result2586_1.nsv", "result2586_2.nsv", "result2586_3.nsv"];
val thyn = "vfmTestDefs2586";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
