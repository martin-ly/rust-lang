" Rust Learning Project Vim Configuration
" Created: 2025-09-25

" Basic Settings
set nocompatible
set number
set relativenumber
set cursorline
set showcmd
set wildmenu
set lazyredraw
set showmatch
set incsearch
set hlsearch
set ignorecase
set smartcase
set autoindent
set smartindent
set expandtab
set tabstop=4
set shiftwidth=4
set softtabstop=4
set wrap
set linebreak
set textwidth=100
set colorcolumn=100

" Rust Specific Settings
autocmd FileType rust setlocal expandtab tabstop=4 shiftwidth=4 softtabstop=4
autocmd FileType rust setlocal textwidth=100 colorcolumn=100
autocmd FileType rust setlocal formatoptions+=t

" Plugin Manager (vim-plug)
call plug#begin('~/.vim/plugged')

" Rust Development
Plug 'rust-lang/rust.vim'
Plug 'racer-rust/vim-racer'
Plug 'timonv/vim-cargo'
Plug 'cespare/vim-toml'

" General Development
Plug 'vim-airline/vim-airline'
Plug 'vim-airline/vim-airline-themes'
Plug 'scrooloose/nerdtree'
Plug 'ctrlpvim/ctrlp.vim'
Plug 'tpope/vim-fugitive'
Plug 'airblade/vim-gitgutter'
Plug 'majutsushi/tagbar'
Plug 'scrooloose/nerdcommenter'
Plug 'tpope/vim-surround'
Plug 'tpope/vim-repeat'
Plug 'junegunn/fzf'
Plug 'junegunn/fzf.vim'

" Code Completion
Plug 'neoclide/coc.nvim', {'branch': 'release'}

call plug#end()

" Key Mappings
let mapleader = " "
nnoremap <leader>w :w<CR>
nnoremap <leader>q :q<CR>
nnoremap <leader>wq :wq<CR>
nnoremap <leader>n :NERDTreeToggle<CR>
nnoremap <leader>f :CtrlP<CR>
nnoremap <leader>b :CtrlPBuffer<CR>
nnoremap <leader>t :TagbarToggle<CR>
nnoremap <leader>g :Git<CR>
nnoremap <leader>d :Git diff<CR>
nnoremap <leader>s :Git status<CR>
nnoremap <leader>c :Git commit<CR>
nnoremap <leader>p :Git push<CR>
nnoremap <leader>l :Git pull<CR>

" Rust Specific Mappings
autocmd FileType rust nnoremap <leader>r :!cargo run<CR>
autocmd FileType rust nnoremap <leader>t :!cargo test<CR>
autocmd FileType rust nnoremap <leader>b :!cargo build<CR>
autocmd FileType rust nnoremap <leader>c :!cargo check<CR>
autocmd FileType rust nnoremap <leader>f :!cargo fmt<CR>
autocmd FileType rust nnoremap <leader>l :!cargo clippy<CR>
autocmd FileType rust nnoremap <leader>d :!cargo doc<CR>
autocmd FileType rust nnoremap <leader>a :!cargo audit<CR>
autocmap FileType rust nnoremap <leader>o :!cargo outdated<CR>

" Colorscheme
colorscheme default
set background=dark

" Status Line
set laststatus=2
let g:airline_theme='dark'
let g:airline#extensions#tabline#enabled = 1

" NERDTree
let g:NERDTreeWinSize = 30
let g:NERDTreeShowHidden = 1

" CtrlP
let g:ctrlp_working_path_mode = 'ra'
let g:ctrlp_user_command = 'ag %s -l --nocolor --hidden -g ""'

" Git Gutter
let g:gitgutter_enabled = 1
let g:gitgutter_map_keys = 0

" Tagbar
let g:tagbar_type_rust = {
    \ 'ctagstype' : 'rust',
    \ 'kinds' : [
        \ 'n:modules',
        \ 's:structs',
        \ 'i:interfaces',
        \ 'c:implementations',
        \ 'f:functions',
        \ 'g:enums',
        \ 't:type aliases',
        \ 'v:constants',
        \ 'M:macros',
        \ 'T:traits',
        \ 'm:methods',
        \ 'e:enums',
        \ 's:statics',
        \ 'r:references',
        \ 'l:lifetimes',
        \ 'a:attributes',
        \ 'u:unsafe',
        \ 'o:operators',
        \ 'p:patterns',
        \ 'd:derives',
        \ 'b:bindings',
        \ 'x:externs',
        \ 'y:types',
        \ 'z:macros',
        \ 'w:where',
        \ 'h:helpers',
        \ 'j:joins',
        \ 'k:keywords',
        \ 'l:lifetimes',
        \ 'm:macros',
        \ 'n:modules',
        \ 'o:operators',
        \ 'p:patterns',
        \ 'r:references',
        \ 's:structs',
        \ 't:traits',
        \ 'u:unsafe',
        \ 'v:constants',
        \ 'w:where',
        \ 'x:externs',
        \ 'y:types',
        \ 'z:macros'
    \ ]
\ }

" CoC Configuration
let g:coc_global_extensions = [
    \ 'coc-rust-analyzer',
    \ 'coc-toml',
    \ 'coc-json',
    \ 'coc-yaml',
    \ 'coc-markdownlint',
    \ 'coc-spell-checker',
    \ 'coc-git',
    \ 'coc-explorer',
    \ 'coc-snippets',
    \ 'coc-pairs',
    \ 'coc-highlight',
    \ 'coc-diagnostic',
    \ 'coc-lists',
    \ 'coc-grep',
    \ 'coc-fzf-preview'
\ ]

" CoC Key Mappings
nmap <silent> gd <Plug>(coc-definition)
nmap <silent> gy <Plug>(coc-type-definition)
nmap <silent> gi <Plug>(coc-implementation)
nmap <silent> gr <Plug>(coc-references)
nmap <silent> [g <Plug>(coc-diagnostic-prev)
nmap <silent> ]g <Plug>(coc-diagnostic-next)
nmap <silent> <leader>rn <Plug>(coc-rename)
nmap <silent> <leader>qf <Plug>(coc-fix-current)
nmap <silent> <leader>ac <Plug>(coc-codeaction)
nmap <silent> <leader>re <Plug>(coc-codeaction-refactor)
nmap <silent> <leader>cl <Plug>(coc-codelens-action)
nmap <silent> <leader>fo <Plug>(coc-format)
nmap <silent> <leader>fs <Plug>(coc-format-selected)
nmap <silent> <leader>fi <Plug>(coc-fix-current)
nmap <silent> <leader>fd <Plug>(coc-diagnostic)
nmap <silent> <leader>fm <Plug>(coc-format)
nmap <silent> <leader>fp <Plug>(coc-fix-current)
nmap <silent> <leader>fr <Plug>(coc-references)
nmap <silent> <leader>ft <Plug>(coc-type-definition)
nmap <silent> <leader>fu <Plug>(coc-references)
nmap <silent> <leader>fv <Plug>(coc-diagnostic)
nmap <silent> <leader>fw <Plug>(coc-diagnostic)
nmap <silent> <leader>fx <Plug>(coc-diagnostic)
nmap <silent> <leader>fy <Plug>(coc-diagnostic)
nmap <silent> <leader>fz <Plug>(coc-diagnostic)
