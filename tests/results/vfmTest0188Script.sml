Theory vfmTest0188[no_sig_docs]
Ancestors vfmTestDefs0188
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0188_0.nsv", "result0188_1.nsv", "result0188_2.nsv", "result0188_3.nsv", "result0188_4.nsv"];
val thyn = "vfmTestDefs0188";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
