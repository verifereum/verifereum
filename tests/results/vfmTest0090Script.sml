Theory vfmTest0090[no_sig_docs]
Ancestors vfmTestDefs0090
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0090_0.nsv", "result0090_1.nsv", "result0090_2.nsv", "result0090_3.nsv"];
val thyn = "vfmTestDefs0090";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
