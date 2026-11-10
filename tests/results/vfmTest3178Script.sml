Theory vfmTest3178[no_sig_docs]
Ancestors vfmTestDefs3178
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3178_0.nsv", "result3178_1.nsv", "result3178_2.nsv", "result3178_3.nsv", "result3178_4.nsv", "result3178_5.nsv", "result3178_6.nsv", "result3178_7.nsv"];
val thyn = "vfmTestDefs3178";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
