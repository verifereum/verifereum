Theory vfmTest0039[no_sig_docs]
Ancestors vfmTestDefs0039
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0039_0.nsv", "result0039_1.nsv", "result0039_2.nsv", "result0039_3.nsv", "result0039_4.nsv", "result0039_5.nsv"];
val thyn = "vfmTestDefs0039";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
