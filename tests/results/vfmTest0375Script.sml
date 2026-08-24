Theory vfmTest0375[no_sig_docs]
Ancestors vfmTestDefs0375
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0375_0.nsv", "result0375_1.nsv", "result0375_2.nsv", "result0375_3.nsv", "result0375_4.nsv", "result0375_5.nsv"];
val thyn = "vfmTestDefs0375";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
