Theory vfmTest0093[no_sig_docs]
Ancestors vfmTestDefs0093
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0093_0.nsv", "result0093_1.nsv", "result0093_2.nsv", "result0093_3.nsv", "result0093_4.nsv", "result0093_5.nsv"];
val thyn = "vfmTestDefs0093";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
