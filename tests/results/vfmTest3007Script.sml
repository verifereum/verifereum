Theory vfmTest3007[no_sig_docs]
Ancestors vfmTestDefs3007
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3007_0.nsv", "result3007_1.nsv", "result3007_2.nsv"];
val thyn = "vfmTestDefs3007";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
