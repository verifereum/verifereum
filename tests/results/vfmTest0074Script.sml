Theory vfmTest0074[no_sig_docs]
Ancestors vfmTestDefs0074
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0074_0.nsv", "result0074_1.nsv", "result0074_2.nsv", "result0074_3.nsv"];
val thyn = "vfmTestDefs0074";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
