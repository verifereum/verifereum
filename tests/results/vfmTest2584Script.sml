Theory vfmTest2584[no_sig_docs]
Ancestors vfmTestDefs2584
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2584_0.nsv", "result2584_1.nsv", "result2584_2.nsv", "result2584_3.nsv"];
val thyn = "vfmTestDefs2584";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
