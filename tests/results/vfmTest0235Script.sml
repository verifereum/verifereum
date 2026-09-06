Theory vfmTest0235[no_sig_docs]
Ancestors vfmTestDefs0235
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0235_0.nsv", "result0235_1.nsv", "result0235_2.nsv", "result0235_3.nsv", "result0235_4.nsv"];
val thyn = "vfmTestDefs0235";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
