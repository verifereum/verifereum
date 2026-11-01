Theory vfmTest3147[no_sig_docs]
Ancestors vfmTestDefs3147
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3147_0.nsv", "result3147_1.nsv", "result3147_2.nsv", "result3147_3.nsv"];
val thyn = "vfmTestDefs3147";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
