Theory vfmTest0117[no_sig_docs]
Ancestors vfmTestDefs0117
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0117_0.nsv", "result0117_1.nsv", "result0117_2.nsv"];
val thyn = "vfmTestDefs0117";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
