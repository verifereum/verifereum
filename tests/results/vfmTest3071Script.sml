Theory vfmTest3071[no_sig_docs]
Ancestors vfmTestDefs3071
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3071_0.nsv", "result3071_1.nsv", "result3071_2.nsv", "result3071_3.nsv"];
val thyn = "vfmTestDefs3071";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
