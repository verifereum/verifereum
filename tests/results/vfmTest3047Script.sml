Theory vfmTest3047[no_sig_docs]
Ancestors vfmTestDefs3047
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3047_0.nsv", "result3047_1.nsv", "result3047_2.nsv", "result3047_3.nsv", "result3047_4.nsv", "result3047_5.nsv", "result3047_6.nsv", "result3047_7.nsv"];
val thyn = "vfmTestDefs3047";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
