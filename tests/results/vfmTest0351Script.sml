Theory vfmTest0351[no_sig_docs]
Ancestors vfmTestDefs0351
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0351_0.nsv", "result0351_1.nsv", "result0351_2.nsv", "result0351_3.nsv", "result0351_4.nsv", "result0351_5.nsv"];
val thyn = "vfmTestDefs0351";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
