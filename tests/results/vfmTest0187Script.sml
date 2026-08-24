Theory vfmTest0187[no_sig_docs]
Ancestors vfmTestDefs0187
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0187_0.nsv", "result0187_1.nsv", "result0187_2.nsv", "result0187_3.nsv"];
val thyn = "vfmTestDefs0187";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
