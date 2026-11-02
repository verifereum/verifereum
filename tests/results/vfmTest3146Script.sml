Theory vfmTest3146[no_sig_docs]
Ancestors vfmTestDefs3146
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3146_0.nsv", "result3146_1.nsv", "result3146_2.nsv", "result3146_3.nsv"];
val thyn = "vfmTestDefs3146";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
