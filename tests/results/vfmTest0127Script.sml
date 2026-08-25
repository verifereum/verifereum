Theory vfmTest0127[no_sig_docs]
Ancestors vfmTestDefs0127
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0127_0.nsv", "result0127_1.nsv", "result0127_2.nsv", "result0127_3.nsv"];
val thyn = "vfmTestDefs0127";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
