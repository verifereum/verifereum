Theory vfmTest0311[no_sig_docs]
Ancestors vfmTestDefs0311
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0311_0.nsv", "result0311_1.nsv", "result0311_2.nsv", "result0311_3.nsv"];
val thyn = "vfmTestDefs0311";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
