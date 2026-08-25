Theory vfmTest0157[no_sig_docs]
Ancestors vfmTestDefs0157
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0157_0.nsv", "result0157_1.nsv", "result0157_2.nsv", "result0157_3.nsv", "result0157_4.nsv"];
val thyn = "vfmTestDefs0157";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
