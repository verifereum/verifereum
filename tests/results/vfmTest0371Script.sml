Theory vfmTest0371[no_sig_docs]
Ancestors vfmTestDefs0371
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0371_0.nsv", "result0371_1.nsv", "result0371_2.nsv", "result0371_3.nsv", "result0371_4.nsv", "result0371_5.nsv", "result0371_6.nsv", "result0371_7.nsv"];
val thyn = "vfmTestDefs0371";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
